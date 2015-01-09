  <!--
\begin{code}

{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -fcontext-stack=100 #-}

module Paper where

import Data.Maybe (fromJust)

import qualified Data.TypeRep as TR

deriving instance Show (f (Term f)) => Show (Term f)

(<>) = (.)

(|-¤) :: SymTab Type env -> Exp -> Maybe (CompExp Type env)

\end{code}
  -->



Introduction
====================================================================================================

Writing interpreters in strongly typed languages often requires using tagged unions to account for the fact that different sub-expressions of the interpreted language may result in values of different types. Consider the following Haskell data type representing expressions with integers and booleans:

\begin{code}
data Exp where
    LitB :: Bool -> Exp               -- Boolean literal
    LitI :: Int -> Exp                -- Integer literal
    Equ  :: Exp -> Exp -> Exp         -- Equality
    Add  :: Exp -> Exp -> Exp         -- Addition
    If   :: Exp -> Exp -> Exp -> Exp  -- Condition
    Var  :: Name -> Exp               -- Variable
\end{code}

  <!--
\begin{code}
    Let  :: Name -> Exp -> Exp -> Exp         -- Let binding
    Iter :: Name -> Exp -> Exp -> Exp -> Exp  -- Iteration
\end{code}
  -->

\vspace{-0.3cm}

\begin{code}
type Name = String
\end{code}

In order to evaluate `Exp`, we need a representation of values -- booleans and integers -- and an environment mapping bound variables to values:

\begin{code}
data Uni   = B !Bool | I !Int
type Env a = [(Name,a)]
\end{code}

\noindent
Evaluation can then be defined as follows:

\begin{code}
eval_U :: Env Uni -> Exp -> Uni
eval_U env (LitB b)   = B b
eval_U env (LitI i)   = I i
eval_U env (Equ a b)  = case (eval_U env a, eval_U env b) of
                         (B a', B b') -> B (a'==b')
                         (I a', I b') -> B (a'==b')
eval_U env (Add a b)  = case (eval_U env a, eval_U env b) of
                         (I a', I b') -> I (a'+b')
eval_U env (If c t f) = case (eval_U env c, eval_U env t, eval_U env f) of
                         (B c', B t', B f') -> B $ if c' then t' else f'
                         (B c', I t', I f') -> I $ if c' then t' else f'
eval_U env (Var v)    = fromJust $ lookup v env
\end{code}

  <!--

\begin{code}
eval_U env (Let v a b) = eval_U ((v, eval_U env a):env) b

eval_U env (Iter v l i b) = case (eval_U env l, eval_U env i) of
    (I l', i') -> iter l' i' (\s -> eval_U ((v,s):env) b)
\end{code}

  -->

One thing stands out in this definition: There is a lot of pattern matching going on! Not only do we have to match on the constructors of `Exp` -- we also have to eliminate and introduce type tags (`B` and `I`) of interpreted values for every single operation. Such untagging and tagging can have a negative effect on performance.

It should be noted that modern compilers are able to handle some of the tagging efficiently. For example the strict fields in the `Uni` type makes `eval_U` essentially tagless in GHC.[^eval_I] Yet, as our measurements show (Sec.\ \ref{results}), the effect of pattern matching on the `Exp` type can still have a large impact on performance. We will also see that dealing with type tags becomes much more expensive in a compositional setting, where the `Uni` type is composed of smaller types.

[^eval_I]: \lstset{basicstyle=\fontsize{7}{10}\fontencoding{T1}\ttfamily}Its performance is the same as that of a tagless version of `eval_U` in which we use `Int` to represent both integers and booleans (see the function `eval_I` in the paper's source code).

  <!--
\begin{code}
-- For reference, a version of eval_U that uses Int instead of Uni (to show the impact of tags)
eval_I :: Env Int -> Exp -> Int
eval_I env (LitB b)       = b2i b
eval_I env (LitI i)       = i
eval_I env (Equ a b)      = b2i $ eval_I env a == eval_I env b
eval_I env (Add a b)      = eval_I env a + eval_I env b
eval_I env (If c t f)     = if eval_I env c == 1 then eval_I env t else eval_I env f
eval_I env (Var v)        = fromJust $ lookup v env
eval_I env (Let v a b)    = eval_I ((v, eval_I env a):env) b
eval_I env (Iter v l i b) = iter (eval_I env l) (eval_I env i) (\s -> eval_I ((v,s):env) b)

b2i True  = 1
b2i False = 0
\end{code}
  -->

Avoiding Type Tags
------------------

In a dependently typed programming language, type tags can be avoided by letting the return type of `eval_U` depend on the expression\ \cite{augustsson1999exercise,pasalic2002tagless}. This avoids the need for tagged unions in functions like `eval_U`. The standard way to do this in Haskell is to make `Exp` an indexed GADT\ \cite{augustsson1994silly,peytonjones2006simple}, i.e. an expression type `Exp_T` that is indexed by the type it evaluates to, so the evaluator has the following type:

\begin{codex}
eval_T :: ... -> Exp_T a -> a
\end{codex}

This means that an expression of type `Exp_T Int` evaluates to an *actual* `Int` rather than a tagged `Int`, and since the type index may vary in the recursive calls of `eval_T`, there is no longer any need for a tagged union. In order to make evaluation for the original `Exp` type efficient, a partial conversion function from `Exp` to `Exp_T` can be defined, and `eval_T` can then be used to evaluate the converted expression. Such a conversion function is implemented in a blog post by Augustsson\ \cite{augustsson2009more} (though not for the purpose of evaluation).

Although going through a type-indexed expression does get rid of the tags of interpreted values, there are at least two problems with this solution:

  * It requires the definition of an additional data type `Exp_T`. If this data type is only going to be used for evaluation, this seems quite redundant.
  * We still have to pattern match on `Exp_T`, which introduces unnecessary overhead.

Avoiding Tags Altogether
------------------------

The motivation behind this report is to implement expression languages in a compositional style using W. Swierstra's Data Types à la Carte \cite{swierstra2008data}. The idea is to specify independent syntactic constructs as separate composable types, and to define functions over such types using extensible type classes (see Sec.\ \ref{compositional-data-types}). However, a compositional implementation is problematic when it comes to evaluation:

  * *Tagged evaluation* for compositional types requires making both `Exp` and `Uni` compositional types. With Data Types à la Carte, construction and pattern matching for compositional types is generally linear in the degree of modularity, which means that the problems with tagging and pattern matching become much worse as the language is extended.
  * *Tagless evaluation* for compositional types requires making both `Exp` and `Exp_T` compositional. However, a generic representation of `Exp_T` is quite different from that of `Exp`, and having to combine two different data type models just for the purpose of evaluation would make things unnecessarily complicated. Moreover, pattern matching on a compositional `Exp_T` gets more expensive as the language is extended.

An excellent solution to these problems is given in A. Baars and S.D. Swierstra's "Typing Dynamic Typing"\ \cite{baars2002typing}. Their approach is essentially to replace `Exp_T a` by a function `env -> a` where `env` is the runtime environment. One may think of the technique as fusing the conversion from `Exp` to `Exp_T` with the evaluator `eval_T` so that the `Exp_T` representation disappears. Put simply, this approach avoids the problem of having to make a compositional version of `Exp_T`. Not only does this lead to a simpler implementation; it also makes evaluation more efficient, as we get rid of the pattern matching on `Exp_T`.

\bigskip

The rest of the report is organized as follows: Sec.\ \ref{typing-dynamic-typing} gives a simple implementation of Typing Dynamic Typing using modern (GHC) Haskell features. Sec.\ \ref{compositional-implementation} makes the implementation compositional using Data Types à la Carte. Sec.\ \ref{supporting-type-constructors} generalizes the compositional implementation using a novel representation of open type representations. Finally, Sec.\ \ref{results} presents a comparison of different implementations of evaluation in terms of performance.

\bigskip

The source of this report is available as a literate Haskell file.[^SourceCode] Certain parts of the code are elided from the report, but the full definitions are found in the source code. A number of GHC-specific extensions are used.

[^SourceCode]: <https://github.com/emilaxelsson/tagless-eval/blob/master/Paper.lhs>



Typing Dynamic Typing
====================================================================================================

Typing Dynamic Typing is a technique for evaluating untyped expressions without any checking of type tags or pattern matching at run time\ \cite{baars2002typing}. In this section, we will present the technique using the `Exp` type from Sec.\ \ref{introduction}.

Type-Level Reasoning
--------------------

We will start by building a small toolbox for type-level reasoning needed to implement evaluation. At the core of this reasoning is a representation of the types in our expression language:

\begin{code}
data Type a where
    BType :: Type Bool
    IType :: Type Int
\end{code}

\noindent
`Type` is an indexed GADT, which means that pattern matching on its constructors will refine the type index to `Bool` or `Int` depending on the case\ \cite{peytonjones2006simple}.

Consider the following function that converts a value to an integer:

\begin{code}
toInt :: Type a -> a -> Int
toInt BType a = if a then 1 else 0
toInt IType a = a
\end{code}

\noindent
In the first case, matching on `BType` refines the type index to `Bool`, and similarly, in the second case, the index is refined to `Int`. On the right-hand sides, the refined types can be used as *local assumptions*, which means that the result expressions are type-correct even though `a` has different types in the two cases.

Next, we define a type for witnessing type-level constraints:[^Dict]

\begin{code}
data Wit c where
    Wit :: c => Wit c
\end{code}

[^Dict]: \lstset{basicstyle=\fontsize{7}{10}\fontencoding{T1}\ttfamily}The `c` parameter of `Wit` has kind `Constraint`, which is allowed by the recent GHC extension `ConstraintKinds`. `Wit` is available as the type `DICT` in the `constraints` package: <http://hackage.haskell.org/package/constraints>.

\noindent
Similarly to how pattern matching on `BType`/`IType` introduces local constraints in the right-hand sides of `toInt`, pattern matching on `Wit` introduces `c` as a local constraint. A constraint can be e.g. a class constraint such as `(Num a)` or an equality between two types `(a ~ b)`.

Equality witnesses for types in our language are constructed by this function:

\begin{code}
typeEqOLD :: Type a -> Type b -> Maybe (Wit (a ~ b))
typeEqOLD BType BType = Just Wit
typeEqOLD IType IType = Just Wit
typeEqOLD _ _         = Nothing
\end{code}

\noindent
Type equality gives us the ability to coerce types dynamically:

\begin{code}
coerce :: Type a -> Type b -> a -> Maybe b
coerce ta tb a = do
    Wit <- typeEqOLD ta tb
    return a
\end{code}

\noindent
Note how pattern matching on `Wit` allows us to assume that `a` and `b` are equal for the rest of the `do` block. This makes it possible to return `a` as having type `b`. Such coercions are at the core of the compiler that will be defined in Sec.\ \ref{typed-compilation}.

To prepare for the compositional implementation in Sec.\ \ref{compositional-implementation}, we overload `typeEq` on the type representation. The code is shown in Fig.\ \ref{fig:type-reasoning}, where we have also added functions for witnessing `Eq` and `Num` constraints.

\begin{figure}[tp]
\lstset{xleftmargin=1em}
\begin{minipage}{0.57\textwidth}
\begin{code}

class TypeRep t where
  typeEq :: t a -> t b -> Maybe (Wit (a~b))
  witEq  :: t a -> Maybe (Wit (Eq a))
  witNum :: t a -> Maybe (Wit (Num a))


--emptyLine
\end{code}
\end{minipage}
\begin{minipage}{0.43\textwidth}
\begin{code}
instance TypeRep Type where
  typeEq BType BType = Just Wit
  typeEq IType IType = Just Wit
  typeEq _ _         = Nothing
  witEq  BType       = Just Wit
  witEq  IType       = Just Wit
  witNum IType       = Just Wit
  witNum BType       = Nothing
\end{code}
\end{minipage}
\caption{Overloaded witnessing functions.}
\label{fig:type-reasoning}
\end{figure}



Typed Compilation
-----------------

The technique in Typing Dynamic Typing is to convert an untyped expression to a run function `env -> a`, where `env` is the runtime environment (holding values of free variables) and `a` is the result type. This run function will perform completely tagless evaluation -- no checking of type tags and no pattern matching on expression constructors. Thus, the conversion function can be seen as a "compiler" that compiles an expression to a tagless run function.

Since the result type of the run function depends on the expression at hand, we have to hide this type using existential quantification. Compiled expressions are thus defined as:

\begin{code}
data CompExp t env where
    (:::) :: (env -> a) -> t a -> CompExp t env
\end{code}

\noindent
The argument `t a` paired with the run function is meant to be a type representation allowing us to coerce the existential type `a`.

To be able to compile variables, we need a symbol table giving the run function for each variable in scope. For this, we use the previously defined `Env` type:

\begin{code}
type SymTab t env = Env (CompExp t env)
\end{code}

\begin{figure}[tp]
\lstset{xleftmargin=1em}
\begin{code}
(|-) :: SymTab Type env -> Exp -> Maybe (CompExp Type env)
\end{code}\vspace{-0.3cm}
\begin{code}
gamma |- LitB b = return $ (\_ -> b) ::: BType
gamma |- LitI i = return $ (\_ -> i) ::: IType
gamma |- Var v  = lookup v gamma
\end{code}\vspace{-0.3cm}
\begin{minipage}{0.55\textwidth}
\begin{code}
gamma |- Equ a b = do
    a' ::: ta <- gamma |- a
    b' ::: tb <- gamma |- b
    Wit       <- typeEq ta tb
    Wit       <- witEq ta
    let run e = a' e == b' e
    return $ run ::: BType
\end{code}\vspace{-0.3cm}
\begin{code}
gamma |- If c t f = do
    c' ::: BType <- gamma |- c
    t' ::: tt    <- gamma |- t
    f' ::: tf    <- gamma |- f
    Wit          <- typeEq tt tf
    let run e = if c' e then t' e else f' e
    return $ run ::: tt
\end{code}
\end{minipage}
\begin{minipage}{0.45\textwidth}
\begin{code}
gamma |- Add a b = do
    a' ::: ta <- gamma |- a
    b' ::: tb <- gamma |- b
    Wit       <- typeEq ta tb
    Wit       <- witNum ta
    let run e = a' e + b' e
    return $ run ::: ta


--emptyLine
\end{code}
\end{minipage}\vspace{-0.3cm}
\caption{Definition of typed compilation \lstinline!(|-)!.}
\label{fig:typed-compilation}
\end{figure}

  <!--
\begin{code}
gamma |- Let v a b = do
    a' ::: ta <- gamma            |- a
    b' ::: tb <- ext (v,ta) gamma |- b
    return $ (\e -> b' (a' e, e)) ::: tb
gamma |- Iter v l i b = do
    l' ::: IType <- gamma            |- l
    i' ::: ti    <- gamma            |- i
    b' ::: tb    <- ext (v,ti) gamma |- b
    Wit          <- typeEq ti tb
    return $ (\e -> iter (l' e) (i' e) (\s -> b' (s,e))) ::: tb
\end{code}
  -->

The compiler is defined in Fig.\ \ref{fig:typed-compilation}. Compilation of literals always succeeds, and the result is simply a constant function paired with the appropriate type representation. For `Equ`, we recursively compile the arguments and bind their run functions and types. In order to use `==` on the results of these run functions, we first have to prove that the arguments have the same type and that this type is a member of `Eq`. We do this by pattern matching on the witnesses returned from `typeEq` and `witEq`. The use of `do` notation and the `Maybe` monad makes it convenient to combine witnesses for multiple constraints: if any function fails to produce a witness, the whole definition fails to produce a result. If the witnesses are produced successfully, we have the necessary assumptions for `a' e == b' e` to be a well-typed expression. Compilation of `Add` and `If` follows the same principle.

For variables, the result is obtained by a lookup in the symbol table. Note that this lookup may fail, in which case the compiler returns `Nothing`. However, lookup failure can only happen at "compile time" (i.e. in `|-`). If we do get a result from `|-`, this `CompExp` will evaluate variables by their run function applied to the runtime environment of type `env`. If `env` is a lookup table, we can also get lookup failures at run time. But as we will see in the next section, it is possible to make `env` a typed heterogeneous collection, such that no lookup failures can occur at run time.



Local Variables
---------------

Although the `Exp` type contains a constructor for variables, there are no constructs that bind local variables. In order to make the example language more interesting, we add two such constructs:[^ObjFunctions]

\begin{code}
data ExpOLD where
    --dotLine
    LetOLD  :: Name -> Exp -> Exp -> ExpOLD         -- Let binding
    IterOLD :: Name -> Exp -> Exp -> Exp -> ExpOLD  -- Iteration
\end{code}

[^ObjFunctions]: In order to keep the types simple, we avoid adding object-level functions to the language, but the technique in this report also works for functions.

\noindent
The expression `Let "x" a b` binds `"x"` to the expression `a` in the body `b`. The expression `Iter "x" l i b` will perform `l` iterations of the body `b`. In each iteration, the previous state is held in variable `"x"` and the initial state is given by `i`. For example, the following expression computes $2^8$ by iterating `\x -> x+x` eight times:

\begin{code}
exONE = Iter "x" (LitI 8) (LitI 1) (Var "x" `Add` Var "x")
\end{code}

So far, we have left the runtime environment completely abstract. The symbol table determines how each variable extracts a value from this environment. In order to compile the constructs that introduce local variables, we need to be able extend the environment. The following function adds a new name to the symbol table and extends the runtime environment by pairing it with a new value:

\begin{code}
ext :: (Name, t a) -> SymTab t env -> SymTab t (a,env)
ext (v,t) gamma = (v, fst ::: t) : map shift gamma
  where shift (w, get ::: u) = (w, (get <> snd) ::: u)
\end{code}

\noindent
For the new variable, the extraction function is `fst`, and for every other variable, we compose the previous extraction function with `snd`. Extending the environment multiple times leads to a runtime environment of the form `(a,(b,(..., env)))`, which we can see as a list of heterogeneously typed values.

Next, the compilation of `Let` and `Iter`:

\begin{code}
gamma |-¤ Let v a b = do
    a' ::: ta <- gamma            |-¤ a
    b' ::: tb <- ext (v,ta) gamma |-¤ b
    return $ (\e -> b' (a' e, e)) ::: tb
\end{code}\vspace{-0.3cm}
\begin{code}
gamma |-¤ Iter v l i b = do
    l' ::: IType <- gamma            |-¤ l
    i' ::: ti    <- gamma            |-¤ i
    b' ::: tb    <- ext (v,ti) gamma |-¤ b
    Wit          <- typeEq ti tb
    return $ (\e -> iter (l' e) (i' e) (\s -> b' (s,e))) ::: tb
\end{code}

\noindent
In both cases, the body `b` is compiled with an extended symbol table containing the local variable. Likewise, when using the compiled body `b'` in the run function, it is applied to an extended runtime environment with the value of the local variable added to the original environment.

Since `Iter` will be used in the benchmarks in Sec.\ \ref{results}, the semantic function `iter` is defined as a strict tail-recursive loop:

\begin{code}
iter :: Int -> a -> (a -> a) -> a
iter l i b = go l i
  where go !0 !a = a
        go !n !a = go (n-1) (b a)
\end{code}

Evaluation
----------

Using the typed compiler, we can now define the evaluator for `Exp`:

\begin{code}
eval_T :: Type a -> Exp -> Maybe a
eval_T t exp = do
    a ::: ta <- ([] :: SymTab Type ()) |- exp
    Wit      <- typeEq t ta
    return $ a ()
\end{code}

\noindent
The caller has to supply the anticipated type of the expression. This type is used to coerce the compilation result. The expression is assumed to be closed, so we start from an empty symbol table and runtime environment.

Finally, we can try evaluation in GHCi:

\begin{ghci}
*Main> eval_T IType exONE
Just 256
\end{ghci}

Let us take a step back and ponder what has been achieved so far. The problem was to get rid of the tag checking in the `eval_U` function. We have done this by breaking evaluation up in two stages: (1) typed compilation, and (2) running the compiled function. But since the compiler still has to check the types of all sub-expressions, have we really gained anything from this exercise? The crucial point is that since the language contains iteration, the same sub-expression may be evaluated *many times*, while the compiler only traverses the expression *once*. In contrast, `eval_U` (extended with `Iter`) has to perform tag checking and pattern matching at *every* loop iteration.



Compositional Implementation
====================================================================================================

So far, we have only considered a closed expression language, represented by `Exp`, and a closed set of types, represented by `Type`. However, the method developed is general and works for any language of similar structure. As in our previous research\ \cite{axelsson2012generic}, a main aim is to provide a generic library for EDSL implementation. The library should allow modular specification of syntactic constructs and manipulation functions so that an EDSL implementation can be done largely by assembling reusable components.

Compositional Data Types
------------------------

In order to achieve a compositional implementation of tagless evaluation, we need to use open representations of expressions and types. For this, we use the representation in Data Types à la Carte \cite{swierstra2008data}:

\begin{code}
data Term f = In (f (Term f))
\end{code}\vspace{-0.3cm}
\begin{code}
data (f :+: g) a = Inl (f a) | Inr (g a)
infixr :+:
\end{code}

\noindent
`Term` is a fixed-point operator turning a base functor `f` into a recursive data type with a value of `f` in each node. Commonly, `f` is a sum type enumerating the constructors in the represented language. The operator `:+:` is used to combine two functors `f` and `g` to a larger one by tagging `f` nodes with `Inl` and `g` nodes with `Inr`.

A redefinition of our `Exp` type using Data Types à la Carte can look as follows:

\begin{code}
data Arith_F a   = LitI_F Int | Add_F a a
data Logic_F a   = LitB_F Bool | Equ_F a a | If_F a a a
data Binding_F a = Var_F Name | Let_F Name a a | Iter_F Name a a a
\end{code}\vspace{-0.3cm}
\begin{code}
type Exp_C = Term (Arith_F :+: Logic_F :+: Binding_F)
\end{code}

\noindent
Here, we made the somewhat arbitrary choice to divide the constructors into three sub-groups. This will allow us to demonstrate the modularity aspect of the implementation.

\begin{figure}[tp]
\lstset{xleftmargin=1em}
\begin{minipage}{0.42\textwidth}
\begin{code}
class f :<: g where
    inj :: f a -> g a
    prj :: g a -> Maybe (f a)
\end{code}\vspace{-0.3cm}
\begin{code}
instance f :<: (f :+: g) where
    inj         = Inl
    prj (Inl f) = Just f
    prj _       = Nothing
\end{code}
\end{minipage}
\begin{minipage}{0.5\textwidth}
\begin{code}
instance f :<: f where
    inj = id
    prj = Just
\end{code}\vspace{-0.3cm}
\begin{code}
instance (f :<: h) => f :<: (g :+: h) where
    inj         = Inr <> inj
    prj (Inr f) = prj f
    prj _       = Nothing
\end{code}
\end{minipage}
\caption{Automated tagging/untagging of nested sums (Data Types à la Carte). The code uses overlapping instances; see the paper\ \cite{swierstra2008data} for details.}
\label{fig:subsumption}
\end{figure}

A problem with nested sums like `Arith_F :+: Logic_F :+: Binding_F` is that the constructors in this type have several layers of tagging. For example, a simple expression representing the variable `"x"` is constructed as follows:

\begin{code}
vExp = In $ Inr $ Inr $ Var_F "x" :: Exp_C
\end{code}

\noindent
Similarly, pattern matching on nested sums quickly becomes unmanageable. The solution provided in Data Types à la Carte is to automate tagging and untagging by means of the type class in Fig.\ \ref{fig:subsumption}. Informally, a constraint `f :<: g` means that `g` is a nested sum in which `f` appears as a term. This class allows us to write the above example as follows:

\begin{code}
vExp' = In $ inj $ Var_F "x" :: Exp_C
\end{code}

\noindent
Importantly, this latter definition is immune to changes in the `Exp_C` type (such as adding a new functor to the sum).

Compositional Evaluation
------------------------

To make the typed compiler from Sec.\ \ref{typing-dynamic-typing} compositional, we simply introduce a type class parameterized on the type representation and the base functor:

\begin{code}
class Compile t f where
    compile_F :: Compile t g
             => SymTab t env -> f (Term g) -> Maybe (CompExp t env)
\end{code}

\noindent
The constraint `Compile t g` makes it possible to recursively compile the sub-terms. Sub-terms have type `Term g` rather than `Term f`. This is so that `f` can be a smaller functor that appears as a part of `g`. For example, in the instance for `Logic_F`, `g` can be the sum `Arith_F:+:Logic_F:+:Binding_F`.

The main compilation function just unwraps the term and calls `compile_F`:

\begin{code}
compile :: Compile t f => SymTab t env -> Term f -> Maybe (CompExp t env)
compile gamma (In f) = compile_F gamma f
\end{code}

The reason for parameterizing `Compile` on the type representation is to be able to compile using different type representations and not be locked down to a particular set of types (such as `Type`). In order to be maximally flexible in the set of types, we can use Data Types à la Carte also to compose type representations. To do this, we break up `Type` into two smaller types:

\begin{code}
data BType a where BType_C :: BType Bool
data IType a where IType_C :: IType Int
\end{code}

\noindent
The relevant `TypeRep` instances are given in Fig.\ \ref{fig:open-type-reasoning}. Using `:+:`, we can compose those into a representation that is isomorphic to `Type`:

\begin{code}
type Type_C = BType :+: IType
\end{code}

\begin{figure}[tp]
\lstset{xleftmargin=1em}
\begin{minipage}{0.5\textwidth}
\begin{code}
instance TypeRep BType where
    typeEq BType_C BType_C = Just Wit
    witEq  BType_C        = Just Wit
    witNum BType_C        = Nothing
\end{code}
\end{minipage}
\begin{minipage}{0.5\textwidth}
\begin{code}
instance TypeRep IType where
    typeEq IType_C IType_C = Just Wit
    witEq  IType_C        = Just Wit
    witNum IType_C        = Just Wit
\end{code}
\end{minipage}\vspace{-0.3cm}
\begin{code}
instance (TypeRep t1, TypeRep t2) => TypeRep (t1 :+: t2) where
    typeEq (Inl t1) (Inl t2) = typeEq t1 t2
    typeEq (Inr t1) (Inr t2) = typeEq t1 t2
    typeEq _ _               = Nothing
    witEq  (Inl t) = witEq t;  witEq  (Inr t) = witEq t
    witNum (Inl t) = witNum t; witNum (Inr t) = witNum t
\end{code}
\caption{\lstinline|TypeRep| instances for compositional type representations.}
\label{fig:open-type-reasoning}
\end{figure}

The `Compile` instance for `ArithF` looks as follows:[^UndecidableInstances]

[^UndecidableInstances]: \lstset{basicstyle=\fontsize{7}{10}\fontencoding{T1}\ttfamily}This instance requires turning on the `UndecidableInstances` extension. In this case, however, the undecidability poses no problems.

\begin{code}
instance (TypeRep t, IType :<: t) => Compile t Arith_F where
    compile_F gamma (LitI_F i)  = return $ const i ::: inj IType_C
    compile_F gamma (Add_F a b) = do
        a' ::: ta <- compile gamma a
        b' ::: tb <- compile gamma b
        Wit       <- typeEq ta tb
        Wit       <- witNum ta
        return $ (\e -> a' e + b' e) ::: ta
\end{code}

  <!--
\begin{code}
instance (TypeRep t, BType :<: t) => Compile t Logic_F where
    compile_F gamma (LitB_F b)  = return $ const b ::: inj BType_C
    compile_F gamma (Equ_F a b) = do
        a' ::: ta <- compile gamma a
        b' ::: tb <- compile gamma b
        Wit       <- typeEq ta tb
        Wit       <- witEq ta
        return $ (\e -> a' e == b' e) ::: inj BType_C
    compile_F gamma (If_F c t f) = do
        c' ::: tc <- compile gamma c
        t' ::: tt <- compile gamma t
        f' ::: tf <- compile gamma f
        Wit       <- typeEq tc (inj BType_C)
        Wit       <- typeEq tt tf
        return $ (\e -> if c' e then t' e else f' e) ::: tt
\end{code}\vspace{-0.3cm}
\begin{code}
instance (TypeRep t, IType :<: t) => Compile t Binding_F where
    compile_F gamma (Var_F v)        = lookup v gamma
    compile_F gamma (Let_F v a b)    = do
        a' ::: ta <- compile gamma a
        b' ::: tb <- compile (ext (v,ta) gamma) b
        return $ (\e -> b' (a' e, e)) ::: tb
    compile_F gamma (Iter_F v l i b) = do
        l' ::: tl <- compile gamma l
        i' ::: ti <- compile gamma i
        b' ::: tb <- compile (ext (v,ti) gamma) b
        Wit       <- typeEq tl (inj IType_C)
        Wit       <- typeEq ti tb
        return $ (\e -> iter (l' e) (i' e) (\s -> b' (s,e))) ::: tb
\end{code}\vspace{-0.3cm}
\begin{code}
instance (Compile t f, Compile t g) => Compile t (f :+: g) where
    compile_F gamma (Inl f) = compile_F gamma f
    compile_F gamma (Inr f) = compile_F gamma f
\end{code}
  -->

\noindent
The close similarity to the code in Fig.\ \ref{fig:typed-compilation} should make the instance self-explanatory. Note how the `t` parameter is left polymorphic, with the minimal constraint `IType :<: t`. This constraint is fulfilled by *any* type representation that includes `IType`. The remaining `Compile` instances are omitted from the report, but can be found in the source code.

We can now define an evaluation function for compositional expressions similar to the definition of `eval_T`:

\begin{code}
eval_C :: forall t f a . (Compile t f, TypeRep t) => t a -> Term f -> Maybe a
eval_C t exp = do
    a ::: ta <- compile ([] :: SymTab t ()) exp
    Wit      <- typeEq t ta
    return $ a ()
\end{code}



Supporting Type Constructors
====================================================================================================

This section might be rather technical, especially for readers not familiar with the generic data type model used\ \cite{axelsson2012generic}. However, it is possible to skip this section and move straight to the results without missing the main points of the report.

The compositional type representations introduced in Sec.\ \ref{compositional-evaluation} have one severe limitation: they do not support type constructors. For example, although it is possible to add a representation for lists of booleans,

\begin{code}
data ListBType a where ListBType :: ListBType [Bool]
\end{code}

\noindent
it is not possible to add a general list type constructor that can be applied to any other type.

In a non-compositional setting, what we would need is something like this:

\begin{code}
data Type_T a where
    BType_T :: Type_T Bool
    IType_T :: Type_T Int
    LType_T :: Type_T a -> Type_T [a]
\end{code}

\noindent
This is a recursive GADT, and to make such a type compositional, we need a compositional data type model that supports type indexes. One such model is *generalized compositional data types*; see section\ 5 of Bahr and Hvitved\ \cite{bahr2011compositional}. Another one is the applicative model by Axelsson\ \cite{axelsson2012generic}. Here we will choose the latter, since it directly exposes the structure of data types without the need for generic helper functions, which leads to a more direct programming style. However, we expect that the former model would work as well.

A Generic Applicative Data Type Model
-------------------------------------

In previous work\ \cite{axelsson2012generic}, we developed a generic data type model that represents data types as primitive symbols and applications:

\begin{code}
data AST sym sig where
    Sym  :: sym sig -> AST sym sig
    (:$) :: AST sym (a :-> sig) -> AST sym (Full a) -> AST sym sig
\end{code}

\noindent
Symbols are introduced from the type `sym` which is a parameter. By using different `sym` types, a wide range of GADTs can be modeled. The `sig` type index gives the symbol's *signature*, which captures its arity as well as the indexes of its arguments and result. Signatures are built using the following two types:

\begin{code}
data Full a
data a :-> sig; infixr :->
\end{code}

\noindent
For example, a symbol with signature `Int :-> Full Bool` represents a unary constructor whose argument is indexed by `Int` and whose result is indexed by `Bool`.

We demonstrate the use of `AST` by defining typed symbols for the arithmetic sub-language of `Exp` with the expression `1+2` as an example:

\begin{code}
data Arith sig where
    LitINEW :: Int -> Arith (Full Int)
    AddNEW  :: Arith (Int :-> Int :-> Full Int)
\end{code}
\vspace{-0.3cm}
\begin{code}
exTWO = Sym AddNEW :$ Sym (LitINEW 1) :$ Sym (LitINEW 2)   :: AST Arith (Full Int)
  -- 1+2
\end{code}

The `AST` type is similar to `Term` in the sense that it makes a recursive data type from a non recursive one. This observation leads to the insight that we can actually use `:+:` to compose symbols just like we used it to compose base functors. We can, for example, split the `Arith` type above into two parts,

\begin{code}
data LitI sig where LitINEWNEW :: Int -> LitI (Full Int)
data Add  sig where AddNEWNEW  :: Add (Int :-> Int :-> Full Int)
\end{code}

\noindent
giving us the following isomorphism:

\begin{codex}
AST Arith sig  =~  AST (LitI :+: Add) sig
\end{codex}

Compositional Type Representations
----------------------------------

Since the `AST` type is an indexed GADT, pattern matching on its constructors together with the symbol gives rise to type refinement just as for the `Type` representation used earlier. This means that we can use `AST` to get compositional type representations, including support for type constructors. For our old friends, `Bool` and `Int`, the representations look as before, with the addition of `Full` in the type parameter:

\begin{code}
data BType_T2 sig where BType_T2 :: BType_T2 (Full Bool)
data IType_T2 sig where IType_T2 :: IType_T2 (Full Int)
\end{code}

\noindent
Now we can also add a representation for the list type constructor, corresponding to `LType_T` above:

\begin{code}
data LType_T2 sig where LType_T2 :: LType_T2 (a :-> Full [a])
\end{code}

To see how type refinement works for such type representations, we define a generic sum function for representable types:

\begin{code}
type Type_T2 a = AST (BType_T2 :+: IType_T2 :+: LType_T2) (Full a)
\end{code}\vspace{-0.3cm}
\begin{code}
gsum :: Type_T2 a -> a -> Int
gsum (Sym itype) i       | Just IType_T2 <- prj itype = i
gsum (Sym ltype :$ t) as | Just LType_T2 <- prj ltype = sum $ map (gsum t) as
gsum _ _ = 0
\end{code}

\noindent
Integers are returned as they are. For lists, we recursively `gsum` each element and then sum the result. We test `gsum` on a doubly-nested list of integers:

\begin{code}
listListInt :: Type_T2 [[Int]]
listListInt = Sym (inj LType_T2) :$ (Sym (inj LType_T2) :$ Sym (inj IType_T2))
\end{code}
\vspace{-0.3cm}
\begin{ghci}
*Main> gsum listListInt [[1],[2,3],[4,5,6]]
21
\end{ghci}

Unfortunately, the compositional implementation of the methods from the `TypeRep` class for the `AST` type is a bit too involved to be presented here. However, it is available in the `open-typerep` package on Hackage.[^open-typerep] Part of the API is listed in Fig.\ \ref{fig:open-typerep-API}.

[^open-typerep]: <http://hackage.haskell.org/package/open-typerep-0.1>

  <!--
\begin{code}
type TypeRepNEW = TR.TypeRep

boolType  = TR.boolType
intType   = TR.intType
listType  = TR.listType
typeEqNEW = TR.typeEq
matchConM = TR.matchConM
\end{code}
  -->

\begin{figure}[tp]
\lstset{xleftmargin=1em}
\begin{code}
newtype TypeRepNEWENW t a = TypeRep (AST t (Full a))
\end{code}\vspace{-0.3cm}
\begin{code}
-- Constructing type reps
boolType :: (TR.BoolType TR.:<: t) => TypeRepNEW t Bool
intType  :: (TR.IntType  TR.:<: t) => TypeRepNEW t Int
listType :: (TR.ListType TR.:<: t) => TypeRepNEW t a -> TypeRepNEW t [a]
\end{code}\vspace{-0.3cm}
\begin{code}
-- Type equality
typeEqNEW :: TR.TypeEq ts ts => TypeRepNEW ts a -> TypeRepNEW ts b -> Maybe (TR.Dict (a ~ b))
\end{code}\vspace{-0.3cm}
\begin{code}
-- List the arguments of a type constructor representation
matchConM :: Monad m => TypeRepNEW t c -> m [TR.E (TypeRepNEW t)]
\end{code}\vspace{-0.3cm}
\begin{code}
-- Existential quantification
data E e where E :: e a -> E e
\end{code}
\caption{Parts of the \lstinline|open-typerep| API.}
\label{fig:open-typerep-API}
\end{figure}

To demonstrate the use of the list type, we extend our language with constructs for introducing and eliminating lists:

\begin{code}
data List_F a = Single a | Cons a a | Head a | Tail a
\end{code}

\noindent
We use a singleton constructor instead of a constructor for empty lists, because we have to be able to assign a monomorphic type representation to each sub-expression, and the empty list gives no information about the type of its elements. (The alternative would be to use a `Nil` constructor that takes a type representation as argument.)

Compilation of `List_F` can be defined as follows:[^CompileIncompatible]

[^CompileIncompatible]: \lstset{basicstyle=\fontsize{7}{10}\fontencoding{T1}\ttfamily}The `Compile` instance for `List_F` is not directly compatible with the other instances in this report. The `List_F` instance uses `(TypeRepNEW t)` as the type representation, while the other instances just use a constrained `t`. To make the instances compatible, the other instances would have to be rewritten to use the `open-typerep` library.

\begin{code}
instance (TR.ListType TR.:<: t, TR.TypeEq t t) => Compile (TypeRepNEW t) List_F where
    compile_F gamma (Single a) = do
        a' ::: ta <- compile gamma a
        return $ (\e -> [a' e]) ::: listType ta
    compile_F gamma (Head as) = do
        as' ::: tas <- compile gamma as
        [TR.E ta]      <- matchConM tas
        TR.Dict         <- typeEqNEW tas (listType ta)
        return $ (\e -> head (as' e)) ::: ta
    --dotLine
\end{code}

  <!--
\begin{code}
    compile_F gamma (Cons a as) = do
        a'  ::: ta  <- compile gamma a
        as' ::: tas <- compile gamma as
        TR.Dict         <- typeEqNEW tas (listType ta)
        return $ (\e -> a' e : as' e) ::: tas
    compile_F gamma (Tail as) = do
        as' ::: tas <- compile gamma as
        [TR.E ta]      <- matchConM tas
        TR.Dict         <- typeEqNEW tas (listType ta)
        return $ (\e -> tail (as' e)) ::: tas
\end{code}
  -->

\noindent
Note how the code does not mention the `AST` type or its constructors. Type representations are constructed using functions like `listType`, and pattern matching is done using a combination of `matchConM` and `typeEq`. For example, in the `Head` case, the `matchConM` line checks that `tas` is a type constructor of one parameter called `ta`. The next line checks that `tas` is indeed a *list* of `ta`, which gives the type refinement necessary for the run function.



Results
====================================================================================================

To verify the claim that the method in this report achieves efficient evaluation, we have performed some measurements of the speed of the different evaluation functions: `eval_U`[^eval_U], `eval_T` and `eval_C`. However, out of these functions, only `eval_C` is compositional. So to make the comparison meaningful, we have added a compositional version of `eval_U`:

\begin{code}
class Eval_UC u f g where
    eval_UCF :: Env (Term u) -> f (Term g) -> Term u
\end{code}\vspace{-0.3cm}
\begin{code}
eval_UC :: Eval_UC u f f => Env (Term u) -> Term f -> Term u
eval_UC env (In f) = eval_UCF env f
\end{code}

[^eval_U]: \lstset{basicstyle=\fontsize{7}{10}\fontencoding{T1}\ttfamily}In the measurements, `eval_U` has been extended with a case for `Iter`; see the source code for details. Note that `eval_U` is different from the other evaluation functions in that it throws an error rather than return `Nothing` when something goes wrong. However, our measurements show only small differences in time if `eval_U` is rewritten to return `Maybe`.

  <!--
\begin{code}
-- For reference, a version of eval_U that returns Maybe
eval_UM :: Env Uni -> Exp -> Maybe Uni
eval_UM env (LitB b)  = Just $ B b
eval_UM env (LitI i)  = Just $ I i
eval_UM env (Equ a b)
    | Just (B a') <- eval_UM env a
    , Just (B b') <- eval_UM env b
    = Just $ B (a'==b')
    | Just (I a') <- eval_UM env a
    , Just (I b') <- eval_UM env b
    = Just $ B (a'==b')
eval_UM env (Add a b)
    | Just (I a') <- eval_UM env a
    , Just (I b') <- eval_UM env b
    = Just $ I (a'+b')
eval_UM env (If c t f)
    | Just (B c') <- eval_UM env c
    , Just (B t') <- eval_UM env t
    , Just (B f') <- eval_UM env f
    = Just $ B $ if c' then t' else f'
    | Just (B c') <- eval_UM env c
    , Just (I t') <- eval_UM env t
    , Just (I f') <- eval_UM env f
    = Just $ I $ if c' then t' else f'
eval_UM env (Var v)     = lookup v env
eval_UM env (Let v a b) = do
    a' <- eval_UM env a
    eval_UM ((v, a'):env) b
eval_UM env (Iter v l i b) = do
    I l' <- eval_UM env l
    i'   <- eval_UM env i
    iterateM (\s -> eval_UM ((v,s):env) b) i' l'

iterateM :: Monad m => (a -> m a) -> a -> Int -> m a
iterateM f i n = go i n
  where
    go !a !0 = return a
    go !a !n = do
      a' <- f a
      go a' (n-1)
\end{code}
  -->

\noindent
Here we have replaced `Uni` by `Term u`, where `u` is a class parameter so that the universal type can be extended. The `f` parameter is the functor of the current node, and `g` is the functor of the sub-terms (and `f` is meant to be part of `g`).

Here we just give the instance for `Arith`. The remaining instances are in the source code.

\begin{code}
instance (I_F :<: u, Eval_UC u g g) => Eval_UC u Arith_F g where
    eval_UCF env (LitI_F i)  = In $ inj $ I_F i
    eval_UCF env (Add_F a b) = case (eval_UC env a, eval_UC env b) of
        (In a', In b') | Just (I_F a'') <- prj a'
                       , Just (I_F b'') <- prj b'
                      -> In $ inj $ I_F (a''+b'')
\end{code}

  <!--
\begin{code}
instance (Eval_UC u f1 g, Eval_UC u f2 g) => Eval_UC u (f1 :+: f2) g where
    eval_UCF env (Inl f) = eval_UCF env f
    eval_UCF env (Inr f) = eval_UCF env f

instance (B_F :<: u, I_F :<: u, Eval_UC u g g) => Eval_UC u Logic_F g where
    eval_UCF env (LitB_F b)  = In $ inj $ B_F b
    eval_UCF env (Equ_F a b) = case (eval_UC env a, eval_UC env b) of
        (In a', In b') | Just (I_F a'') <- prj a', Just (I_F b'') <- prj b' -> In $ inj $ B_F (a''==b'')
        (In a', In b') | Just (B_F a'') <- prj a', Just (B_F b'') <- prj b' -> In $ inj $ B_F (a''==b'')
    eval_UCF env (If_F c t f) = case (eval_UC env c, eval_UC env t, eval_UC env f) of
        (In c', In t', In f') | Just (B_F c'') <- prj c', Just (B_F t'') <- prj t', Just (B_F f'') <- prj f' -> In $ inj $ B_F $ if c'' then t'' else f''
        (In c', In t', In f') | Just (B_F c'') <- prj c', Just (I_F t'') <- prj t', Just (I_F f'') <- prj f' -> In $ inj $ I_F $ if c'' then t'' else f''

instance (B_F :<: u, I_F :<: u, Eval_UC u g g) => Eval_UC u Binding_F g where
    eval_UCF env (Var_F v)        = fromJust $ lookup v env
    eval_UCF env (Let_F v a b)    = eval_UC ((v, eval_UC env a):env) b
    eval_UCF env (Iter_F v l i b) = case (eval_UC env l, eval_UC env i) of
        (In l',i') | Just (I_F l'') <- prj l' -> iter l'' i' (\s -> eval_UC ((v,s):env) b)
\end{code}
  -->

\noindent
This definition is similar to the `Add` case in `eval_U`, but here we use an open universal type, so tagging and untagging is done using `inj` and `prj` from Fig.\ \ref{fig:subsumption}. The `Uni` type has been decomposed into the following functors:

\begin{code}
data B_F a = B_F !Bool
data I_F a = I_F !Int
\end{code}

As the degree of modularity increases, the functions `eval_C` and `eval_UC` become more expensive. To test this behavior, Fig.\ \ref{fig:eval-sizes} defines specialized evaluation functions for varying sizes of the functor sums. The empty type `X` is introduced just to be able make large functor sums.

\begin{figure}[tp]
\begin{code}
eval_C3   = eval_C     :: Type_3 a  -> Exp_3  -> Maybe a
eval_C10  = eval_C     :: Type_10 a -> Exp_10 -> Maybe a
eval_C30  = eval_C     :: Type_30 a -> Exp_30 -> Maybe a
\end{code}\vspace{-0.3cm}
\begin{code}
eval_UC3  = eval_UC [] :: Exp_3  -> Uni_3
eval_UC10 = eval_UC [] :: Exp_10 -> Uni_10
eval_UC30 = eval_UC [] :: Exp_30 -> Uni_30
\end{code}

\begin{codex}
data X a
instance TypeRep X; instance Compile t X; instance Eval_UC u X g
\end{codex}\vspace{-0.3cm}
\begin{codex}
type Exp_3  = Term (Arith_F :+: Logic_F :+: Binding_F)                  -- 3 terms
type Exp_10 = Term (X:+:X:+: ... :+: Arith_F :+: Logic_F :+: Binding_F) -- 10 terms
type Exp_30 = Term (X:+:X:+: ... :+: Arith_F :+: Logic_F :+: Binding_F) -- 30 terms
\end{codex}\vspace{-0.3cm}
\begin{codex}
type Type_3 = X :+: BType :+: IType
type Uni_3  = Term (X :+: B_F :+: I_F)   -- Etc. for Type_10, Type_30, Uni_10, Uni_30
\end{codex}\vspace{-0.3cm}
\begin{codex}

\end{codex}
\caption{Specialized evaluation functions for variously-sized functors}
\label{fig:eval-sizes}
\end{figure}

  <!--
\begin{code}
data X a

instance TypeRep X where
   typeEq = undefined
   witEq  = undefined
   witNum = undefined

instance Compile t X where compile_F = undefined

instance Eval_UC u X g where eval_UCF = undefined

type Exp_3  = Term (Arith_F :+: Logic_F :+: Binding_F)
type Type_3 = X :+: BType :+: IType
type Uni_3  = Term (X :+: B_F :+: I_F)

type Exp_10  = Term (X :+: X :+: X :+: X :+: X :+: X :+: X :+: Arith_F :+: Logic_F :+: Binding_F)
type Uni_10  = Term (X :+: X :+: X :+: X :+: X :+: X :+: X :+: X :+: B_F :+: I_F)
type Type_10 = X :+: X :+: X :+: X :+: X :+: X :+: X :+: X :+: BType :+: IType

type Exp_30  = Term (X :+: X :+: X :+: X :+: X :+: X :+: X :+: X :+: X :+: X :+: X :+: X :+: X :+: X :+: X :+: X :+: X :+: X :+: X :+: X :+: X :+: X :+: X :+: X :+: X :+: X :+: X :+: Arith_F :+: Logic_F :+: Binding_F)
type Type_30 = X :+: X :+: X :+: X :+: X :+: X :+: X :+: X :+: X :+: X :+: X :+: X :+: X :+: X :+: X :+: X :+: X :+: X :+: X :+: X :+: X :+: X :+: X :+: X :+: X :+: X :+: X :+: X :+: BType :+: IType
type Uni_30  = Term (X :+: X :+: X :+: X :+: X :+: X :+: X :+: X :+: X :+: X :+: X :+: X :+: X :+: X :+: X :+: X :+: X :+: X :+: X :+: X :+: X :+: X :+: X :+: X :+: X :+: X :+: X :+: X :+: B_F :+: I_F)
\end{code}
  -->

The first benchmark is for a balanced addition tree of depth 18, where we get the following results:[^ReproducibleBenchmarks]

[^ReproducibleBenchmarks]: \lstset{basicstyle=\fontsize{7}{10}\fontencoding{T1}\ttfamily}All measurements were done on a Dell laptop with an Intel Core i7-4600U processor and GHC 7.8.3 with the `-O2` flag.

\vspace{-0.3cm}
\begin{multicols}{2}
\begin{ghci}
eval_U addTree: 0.0046s
eval_T addTree: 0.034s
\end{ghci}
\begin{ghci}
eval_C3  addTree: 0.19s
eval_UC3 addTree: 0.011s
\end{ghci}
\end{multicols}
\vspace{-0.2cm}

\noindent
In this case, the expression is very large, and the cost of compiling the expression is proportional to the cost of evaluating it. In such cases, typed compilation does not give any benefits, and we are better off using `eval_UC` for compositional evaluation. However, such huge expressions are quite rare. It is much more common to have small expressions that are costly to evaluate.

Our next benchmark is a triply-nested loop with `n` iterations at each level:

\begin{code}
loopNestOLD :: Int -> Exp
loopNestOLD n = Iter "x" (LitI n) (LitI 0) $
               Iter "y" (LitI n) (Var "x") $
                 Iter "z" (LitI n) (Var "y") $
                   (Var "x" `Add` Var "y" `Add` Var "z" `Add` LitI 1)
\end{code}

\noindent
This is a small expression, but it is costly to evaluate. For the expression `loopNest 100`, the results are as follows:

\vspace{-0.2cm}
\begin{multicols}{2}
\begin{ghci}
eval_U   loopNest: 0.14s
eval_T   loopNest: 0.042s
eval_C3  loopNest: 0.073s
eval_UC3 loopNest: 0.17s
\end{ghci}

\begin{ghci}
eval_C10  loopNest: 0.077s
eval_UC10 loopNest: 0.27s
eval_C30  loopNest: 0.074s
eval_UC30 loopNest: 0.75s
\end{ghci}
\end{multicols}

Now we see in the first column that evaluation based on typed compilation is clearly superior. Even more interestingly, the second column shows what happens as we increase the degree of modularity: the timing for `eval_C*` stays roughly constant, while the timing for `eval_UC*` grows significantly with the modularity. The reason why typed compilation is immune to extension is that compositional data types are only present during the compilation stage, and this stage is very fast for a small expression like `loopNest 100`.

As a reference point, we have also measured the function

\begin{code}
loopNest_HOLD :: Int -> Int
loopNest_HOLD n = iter n 0 $ \x -> iter n x $ \y -> iter n y $ \z -> x+y+z+1
\end{code}

\noindent
which runs the expression corresponding to `loopNest` directly in Haskell. This function runs around $40\times$ faster than `eval_T` (for `n = 100`). This is not surprising, given that `loopNest_H` is subject to GHC's `-O2` optimizations. We think of the typed compilation technique (Sec.\ \ref{typed-compilation}) as a compiler in the sense that it removes interpretive overhead before running a function. However, the result of typed compilation is generated at run time, so it will of course not be subject to GHC's optimizations. Interestingly, when `loopNest_H 100` is compiled with `-O0`, it runs at the same speed as `eval_T` compiled with `-O2`. Thus, this benchmark shows that it is not unreasonable to expect an embedded evaluator to run on par with unoptimized, compiled Haskell code.



Conclusion and Related Work
====================================================================================================

We have presented an implementation of evaluation for compositional expressions based on Typing Dynamic Typing\ \cite{baars2002typing}. The overhead due to compositional types is only present in the initial compilation stage. After compilation, a tagless evaluation function is obtained which performs evaluation completely without pattern matching or risk of getting stuck. This makes the method suitable e.g. for evaluating embedded languages based on compositional data types.

The final tagless technique by Carette et al.\ \cite{carette2009finally} models languages using type classes, which makes the technique inherently tagless and compositional. However, in order to avoid tag checking of interpreted values, expressions have to be indexed on the interpreted type, just like in a GADT-based solution\ \cite{peytonjones2006simple}. If, for some reason, we start with an untyped representation of expressions (e.g. resulting from parsing), the only way to get to a type-indexed tagless expression is by means of typed compilation, e.g. as in this report. Typed compilation to final tagless terms has been implemented by Kiselyov\ \cite{kiselyovtyped} (for non-compositional representations of source expressions).

  <!--
TODO One could make a deal about the fact that the method in this report has constrained polymorphic rules for operations like addition and equality. The implementations in \cite{augustsson2009more, kiselyovtyped} do not have this.
  -->

Bahr has worked on evaluation for compositional data types\ \cite{bahr2011evaluation}. However, his work focuses on evaluation strategies rather than tag elimination.



  <!--
====================================================================================================
  -->

\subsubsection*{Acknowledgements}

\noindent
{\small This work is funded by the Swedish Foundation for Strategic Research, under grant RAWFP. David Raymond Christiansen, Gabor Greif and the anonymous referees for TFP 2014 provided useful feedback on this report.}

