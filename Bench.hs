{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeOperators #-}

{-# OPTIONS_GHC -fcontext-stack=100 #-}

import Numeric
import Data.Foldable (Foldable)
import qualified Data.Foldable as Foldable
import Data.Maybe (fromJust)
import Data.Time
import Paper



deriving instance (Functor  f, Functor  g) => Functor  (f :+: g)
deriving instance (Foldable f, Foldable g) => Foldable (f :+: g)
deriving instance Functor  Arith_F
deriving instance Foldable Arith_F
deriving instance Functor  Logic_F
deriving instance Foldable Logic_F
deriving instance Functor  Binding_F
deriving instance Foldable Binding_F
deriving instance Functor  X
deriving instance Foldable X



-- | Evaluate a name to normal form
nameNf :: Name -> ()
nameNf v = sum (map fromEnum v) `seq` ()

-- | Evaluate an expression to normal form
expNf :: Exp -> ()
expNf (LitB b)       = b `seq` ()
expNf (LitI i)       = i `seq` ()
expNf (Equ a b)      = expNf a `seq` expNf b
expNf (Add a b)      = expNf a `seq` expNf b
expNf (If c t f)     = expNf c `seq` expNf t `seq` expNf f
expNf (Var v)        = nameNf v `seq` ()
expNf (Let v a b)    = nameNf v `seq` expNf a `seq` expNf b `seq` ()
expNf (Iter v l i b) = nameNf v `seq` expNf l `seq` expNf i `seq` expNf b `seq` ()

-- | Evaluate a compositional expression to normal form
expNfG :: (Binding_F :<: f, Functor f, Foldable f) => Term f -> ()
expNfG (In f)
    | Just (Var_F v) <- prj f = nameNf v
expNfG (In f) = null [() | () <- Foldable.toList $ fmap expNfG f] `seq` ()

-- | Balanced addition tree of depth n
addTree :: Int -> Exp
addTree 0 = LitI 10
addTree n = addTree (n-1) `Add` addTree (n-1)

-- | Balanced addition tree of depth n
addTree_C :: (Arith_F :<: f) => Int -> Term f
addTree_C 0 = In $ inj (LitI_F 10)
addTree_C n = In $ inj $ addTree_C (n-1) `Add_F` addTree_C (n-1)

addTreeFixed = Let "x" (addTree 18) (Var "x")

addTreeFixed_C :: Exp_3
addTreeFixed_C = In $ inj $ Let_F "x" (addTree_C 18) (In $ inj $ Var_F "x")

addTreeFixed_C10 :: Exp_10
addTreeFixed_C10 = In $ inj $ Let_F "x" (addTree_C 18) (In $ inj $ Var_F "x")

addTreeFixed_C30 :: Exp_30
addTreeFixed_C30 = In $ inj $ Let_F "x" (addTree_C 18) (In $ inj $ Var_F "x")

-- | Create a triply nested loop with n iterations at each level
loopNest :: Int -> Exp
loopNest n =
    Iter "x" (LitI n) (LitI 0) $
      Iter "y" (LitI n) (Var "x") $
        Iter "z" (LitI n) (Var "y") $
          (Var "x" `Add` Var "y" `Add` Var "z" `Add` LitI 1)

-- | For reference, same computation in plain Haskell
loopNest_H :: Int -> Int
loopNest_H n = iter n 0 $ \x -> iter n x $ \y -> iter n y $ \z -> x + y + z + 1

-- | Create a triply nested loop with n iterations at each level
loopNest_C :: (Arith_F :<: f, Binding_F :<: f) => Int -> Term f
loopNest_C n =
    iter "x" (lit n) (lit 0) $
      iter "y" (lit n) (var "x") $
        iter "z" (lit n) (var "y") $
          (var "x" <+> var "y" <+> var "z" <+> lit 1)
  where
    lit i        = In $ inj $ LitI_F i
    a <+> b      = In $ inj $ Add_F a b
    var v        = In $ inj $ Var_F v
    iter v l i b = In $ inj $ Iter_F v l i b

loopNestFixed = loopNest 100

loopNestFixed_C :: Exp_3
loopNestFixed_C = loopNest_C 100

loopNestFixed_C10 :: Exp_10
loopNestFixed_C10 = loopNest_C 100

loopNestFixed_C30 :: Exp_30
loopNestFixed_C30 = loopNest_C 100

u2i :: Uni -> Int
u2i (I i) = i

u2i' :: (I_F :<: u) => Term u -> Int
u2i' (In f) | Just (I_F i) <- prj f = i

eval_U' :: Exp -> Maybe Int
eval_U' = Just . u2i . eval_U []

eval_I' :: Exp -> Maybe Int
eval_I' = Just . eval_I []

eval_T' :: Exp -> Maybe Int
eval_T' = eval_T IType

eval_C3', eval_UC3' :: Exp_3 -> Maybe Int
eval_C3'  = eval_C3 (inj IType_C)
eval_UC3' = Just . u2i' . eval_UC3

eval_C10', eval_UC10' :: Exp_10 -> Maybe Int
eval_C10'  = eval_C10 (inj IType_C)
eval_UC10' = Just . u2i' . eval_UC10

eval_C30', eval_UC30' :: Exp_30 -> Maybe Int
eval_C30'  = eval_C30 (inj IType_C)
eval_UC30' = Just . u2i' . eval_UC30



----------------------------------------------------------------------------------------------------
-- Benchmarks
----------------------------------------------------------------------------------------------------

data Bench = Bench String (IO ())

fill :: [(String,a)] -> [(String,a)]
fill [] = []
fill ls = [(a ++ ": " ++ replicate d ' ', b) | (a,b) <- ls, let d = w - length a]
  where
    w = maximum $ map (length.fst) ls

-- | Show a time difference using @n@ significant figures
showSignificant :: Int -> NominalDiffTime -> String
showSignificant n a = showFFloat Nothing b "s"
  where
    ae = showEFloat (Just (n-1)) (fromRational $ toRational a) ""
    b  = read ae :: Double

runBench :: [Bench] -> IO ()
runBench bs = do
    tab <- fmap fill . go bs [] =<< getCurrentTime
    putStrLn "--------------------"
    putStr $ unlines $ map (uncurry (++)) tab
  where
    go [] rs _ = return $ reverse rs
    go (Bench name b : bs) rs t = do
        b
        t' <- getCurrentTime
        go bs ((name, showSignificant 2 $ diffUTCTime t' t) : rs) t'

benchmarks1 =
    [ Bench "eval_U addTree" $ print $ eval_U'   addTreeFixed
    , Bench "eval_I addTree" $ print $ eval_I'   addTreeFixed
    , Bench "eval_T addTree" $ print $ eval_T'   addTreeFixed
    , Bench "eval_C3  addTree" $ print $ eval_C3'  addTreeFixed_C
    , Bench "eval_UC3 addTree" $ print $ eval_UC3' addTreeFixed_C
    ]

benchmarks2 =
    [ Bench "eval_U   loopNest" $ print $ eval_U'   loopNestFixed
    , Bench "eval_I   loopNest" $ print $ eval_I'   loopNestFixed
    , Bench "eval_T   loopNest" $ print $ eval_T'   loopNestFixed
    , Bench "eval_C3  loopNest" $ print $ eval_C3'  loopNestFixed_C
    , Bench "eval_UC3 loopNest" $ print $ eval_UC3' loopNestFixed_C
    , Bench "haskell  loopNest" $ print $ loopNest_H 100
    ]

benchmarks3 =
    [ Bench "eval_C10  loopNest" $ print $ eval_C10'  loopNestFixed_C10
    , Bench "eval_C30  loopNest" $ print $ eval_C30'  loopNestFixed_C30
    , Bench "eval_UC10 loopNest" $ print $ eval_UC10' loopNestFixed_C10
    , Bench "eval_UC30 loopNest" $ print $ eval_UC30' loopNestFixed_C30
    ]

benchmarks4 =
    [ Bench "eval_UM addTree"  $ print $ u2i $ fromJust $ eval_UM [] addTreeFixed
    , Bench "eval_UM loopNest" $ print $ u2i $ fromJust $ eval_UM [] loopNestFixed
    ]


main = do
    -- Make sure that expressions are evaluated
    case expNf addTreeFixed       of () -> return ()
    case expNfG addTreeFixed_C    of () -> return ()
    case expNfG addTreeFixed_C10  of () -> return ()
    case expNfG addTreeFixed_C30  of () -> return ()
    case expNf loopNestFixed      of () -> return ()
    case expNfG loopNestFixed_C   of () -> return ()
    case expNfG loopNestFixed_C10 of () -> return ()
    case expNfG loopNestFixed_C30 of () -> return ()
    -- Warm up
    print $ eval_U' (loopNest 80)
    print $ eval_U' (loopNest 81)
    print $ eval_U' (loopNest 82)
    -- Benchmarks
    runBench benchmarks1
    runBench benchmarks2
    runBench benchmarks3
    runBench benchmarks4

-- eval_U   addTree: 0.019672s
-- eval_T   addTree: 0.022689s
-- eval_C3  addTree: 0.188947s
-- eval_UC3 addTree: 0.026615s
-- --------------------
-- eval_U   loopNest: 0.504205s
-- eval_T   loopNest: 0.050187s
-- eval_C3  loopNest: 0.070469s
-- eval_UC3 loopNest: 0.52127s
-- haskell  loopNest: 0.001167s
-- --------------------
-- eval_C10  loopNest: 0.07133s
-- eval_C30  loopNest: 0.070431s
-- eval_UC10 loopNest: 0.67257s
-- eval_UC30 loopNest: 1.14117s

-- Speed increase between eval_C* and eval_UC* 7.4x - 16x

-- haskell is ~40x faster than eval_T. When compiling with `-O0`, the difference is ~2.5x.

