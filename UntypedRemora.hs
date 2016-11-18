--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
------------------------------- UntypedRemora.hs -------------------------------
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE TemplateHaskell #-}

module UntypedRemora where

import qualified Control.Exception as CE
import qualified Data.Maybe as DM
import qualified Data.Map.Strict as M
import Data.Typeable.Internal(Typeable)
import Prelude hiding(max)

import Test
--------------------------------------------------------------------------------
---------------------------------- Data Types ----------------------------------
--------------------------------------------------------------------------------

type Identifier = String
type Nat = Int -- I know, I know
type Error = String

type ArrayWithShape a = ([a], [Nat])

getArray :: ArrayWithShape a -> [a]
getArray = fst

getShape :: ArrayWithShape a -> [Nat]
getShape = snd

test_ArrayWithShape = [
    getArray ([1], [0]) `is` [1],
    getShape ([1], [0])`is` [0]
  ]

type IdenRankBinding = (Identifier, Rank)

getIden :: IdenRankBinding -> Identifier
getIden = fst

getRank :: IdenRankBinding -> Rank
getRank = snd

test_IdenRankBinding = [
    getIden ("x", RankFinite 0) `is` "x",
    getRank ("x", RankFinite 1) `is` RankFinite 1,
    getRank ("x", RankInfinite) `is` RankInfinite
  ]

data InternalError = 
      Undefined
    | Msg String
    deriving (Eq, Show, Typeable)

instance CE.Exception InternalError

data Expr =
      EArray Array
    | EIden Identifier
    | EApp [Expr]
    | EUnbox Identifier Expr Expr
    | EVal Val 
    deriving (Eq, Show)

matchesBetaContext :: [Expr] -> [IdenRankBinding] -> Bool
matchesBetaContext vs binds =
  case mapM (rank . getVal) vs of
    Just valRanks -> all isVal vs && (map getRank binds == valRanks) && length vs == length binds
    Nothing       -> False
    
test_matchesBetaContext = [
    matchesBetaContext [] [] `is` True,
    matchesBetaContext [] [("x", RankFinite 0)] `is` False,
    matchesBetaContext [makeTestShapelyEVal []]  [] `is` False,
    matchesBetaContext [makeTestShapelyEVal []]  [("x", RankFinite 0)] `is` True,
    matchesBetaContext (map makeTestShapelyEVal [[1],[1,1],[1,1,1]])  (map (\x -> ("x", RankFinite x)) [1,2,3]) `is` True,
    matchesBetaContext (map makeTestShapelyEVal [[1],[1,1],[1,1,1]])  (map (\x -> ("x", RankFinite x)) [1,2,2]) `is` False,
    matchesBetaContext [makeTestShapelyEVal []]  [("x", RankFinite 1)] `is` False,
    matchesBetaContext [makeTestShapelyEVal [0]] [("x", RankFinite 0)] `is` False,
    matchesBetaContext [makeTestShapelyEVal []]  [("x", RankInfinite)] `is` False,
    matchesBetaContext [makeTestEValInt 0]  [("x", RankFinite 0)] `is` False
  ]



smallStep :: Expr -> Either Error Expr
smallStep (EApp (EArray (AArray ([AFun (FLam binds body)],[])) : vs))
    | matchesBetaContext vs binds = Right $ substExpr (makeEnv binds vs) body
smallStep _ = Left "stuck"

betaPattern binds body vs = (EApp (EArray (AArray ([AFun (FLam binds body)],[])) : vs))

test_smallStep = [
    smallStep (betaPattern
                [("x", RankFinite 0), ("y", RankFinite 1)]
                (EApp [EIden "x", EIden "y"])
                (map makeTestShapelyEVal [[],[1]]))
      `is` Right (EApp (map makeTestShapelyEVal [[],[1]]))
  ]

data Array =
      AArray ([ArrayElement], [Nat])
    | ABox Expr
    deriving (Eq, Show)

data ArrayElement =
      ABase Base
    | AFun Fun
    | AExpr Expr
    deriving (Eq, Show)

data Base =
    BInt Int
    deriving (Eq, Show)

data Fun =
      FPrim Prim
    | FLam [IdenRankBinding] Expr
    deriving (Eq, Show)

data Prim =
      IntUnop (Int -> Int)
    | IntBinop (Int -> Int -> Int)

instance Eq Prim where
    x == y = CE.throw . Msg $ "Don't compare primitive functions for equality!"

instance Show Prim where
    show (IntUnop _)  = "IntUnop <func>"
    show (IntBinop _) = "IntBinop <func>"

data Rank =
      RankFinite Int 
    | RankInfinite
    deriving (Eq, Show)

data Val =
      VBase Base
    | VFun Fun
    | VBaseArray ([Val], [Nat])
    | VFunArray ([Val], [Nat])
    | VBox Val
    | VBoxArray ([Val], [Nat])
    deriving (Eq, Show)

identityFun = FLam [("x", RankInfinite)] (EIden "x")

identityPrim = IntUnop id

makeTestValInt n = VBase $ BInt n
makeTestEValInt n = EVal $ makeTestValInt n

identityFunVal = VFun identityFun

makeTestShapelyVal ns = VBaseArray (replicate (length ns) identityFunVal, ns)
makeTestShapelyEVal = EVal . makeTestShapelyVal

--------------------------------------------------------------------------------
-------------------------------- Util Functions --------------------------------
--------------------------------------------------------------------------------
takeAllButLastN :: Int -> [a] -> [a]
takeAllButLastN n list = take (length list - n) list

dropAllButLastN :: Int -> [a] -> [a]
dropAllButLastN n list = drop (length list - n) list

-- stackoverflow.com/a/8681226
splitEvery :: Int -> [a] -> [[a]]
splitEvery _ [] = []
splitEvery n list = first : splitEvery n rest
  where
    (first, rest) = splitAt n list

--------------------------------------------------------------------------------
-------------------------------- Meta Functions --------------------------------
--------------------------------------------------------------------------------

getVal :: Expr -> Val
getVal (EVal v) = v
getVal _ = CE.throw Undefined

test_getVal = [
    getVal (makeTestEValInt 1) `is` makeTestValInt 1, 
    getVal (EApp []) `raises` Undefined
  ]

isVal :: Expr -> Bool
isVal (EVal _) = True
isVal _ = False

test_isVal = [
    isVal (EVal (VBase (BInt 0))) `is` True,
    isVal (EApp []) `is` False
  ]

makeEnv :: [IdenRankBinding] -> [Expr] -> M.Map Identifier Val
makeEnv binds vs
    | length binds == length vs = M.fromList $ zip (map getIden binds) (map getVal vs)
    | otherwise = CE.throw Undefined

test_makeEnv = [
    makeEnv [] [] `is` M.empty,
    makeEnv [("x", RankFinite 1), ("y", RankInfinite)] [makeTestEValInt 3, makeTestEValInt 4]
     `is` M.fromList [("x", makeTestValInt 3), ("y", makeTestValInt 4)],
    makeEnv [("x", RankFinite 1), ("y", RankInfinite)] [makeTestEValInt 3] `raises` Undefined,
    makeEnv [("x", RankFinite 1)] [makeTestEValInt 3, makeTestEValInt 4] `raises` Undefined,
    makeEnv [("x", RankFinite 1)] [EApp []] `raises` Undefined
  ]

valToArrayWithShape :: Val -> Maybe (ArrayWithShape Val)
valToArrayWithShape (VBaseArray x) = Just x
valToArrayWithShape (VFunArray x)  = Just x
valToArrayWithShape (VBoxArray x)  = Just x
valToArrayWithShape _              = Nothing

-- Fig. 5, Rank
rank :: Val -> Maybe Rank
rank v = valToArrayWithShape v >>= return . RankFinite . length . getShape

test_rank = [
    rank (makeTestShapelyVal []) `is` Just (RankFinite 0),
    rank (makeTestShapelyVal [0,0,0]) `is` Just (RankFinite 3),
    rank (makeTestShapelyVal [1..11]) `is` Just (RankFinite 11),
    rank (makeTestValInt 0) `is` Nothing
  ]

fromRankFinite :: Rank -> Int
fromRankFinite (RankFinite n) = n
fromRankFinite _              = CE.throw Undefined

rankFin :: Val -> Maybe Int
rankFin v = rank v >>= return . fromRankFinite

-- Fig. 5, ArgRank
argrank :: Fun -> [Rank]
argrank (FLam binds _) = map getRank binds

naturalizePair :: (IdenRankBinding, Val) -> Maybe IdenRankBinding
naturalizePair ((x, rho), v) =
  case rho of
    RankFinite p -> 
        if p >= 0
        then return (x, RankFinite p)
        else        rankFin v >>= \n -> return (x, RankFinite (n + p))
    RankInfinite -> rankFin v >>= \n -> return (x, RankFinite n)

-- Fig. 5, Naturalize
naturalize :: Fun -> [Val] -> Maybe Fun
naturalize (FLam binds e) vs | length binds == length vs =
  let newBinds = DM.catMaybes (zipWith (curry naturalizePair) binds vs)
  in
    if length newBinds == length binds
    then Just $ FLam newBinds e
    else Nothing

-- Fig. 5, Frame
frame :: Nat -> Val -> Maybe [Nat]
frame p v = valToArrayWithShape v >>= return . takeAllButLastN p . getShape

isPrefixOf :: Eq a => [a] -> [a] -> Bool
isPrefixOf [] _ = True
isPrefixOf (n:ns) (m:ms) | n == m = ns `isPrefixOf` ms
isPrefixOf _ _ = False

-- Fig. 5, Max
max :: Eq a => [[a]] -> [a]
max [n0] = n0
max (n0:n1:rest) =
      let maxRest = max rest
      in
        if maxRest `isPrefixOf` n0
        then n0
        else if n0 `isPrefixOf` n1
        then maxRest
        else CE.throw Undefined

-- Fig. 5, Dup
dup :: Nat -> [Nat] -> Val -> Val
dup p ns v = v
  --let k   = product $ takeAllButLastN p ns
  --    l's =  cells p v

-- Fig. 5, Cells
cells :: Nat -> [a] -> [Nat] -> [[a]]
cells n ls ns =
    let ds = dropAllButLastN n ns
        m  = product ds
    in splitEvery m ls

shadow :: M.Map Identifier Val -> [Identifier] -> M.Map Identifier Val
shadow env _ | M.null env = env 
shadow env [] = env
shadow env list =
  let x = head list in
    if M.member x env
    then shadow (M.delete x env) list
    else shadow env (tail list)

dummyEnv = M.fromList [
    ("x", makeTestValInt 0),
    ("y", makeTestValInt 1),
    ("z", makeTestValInt 2)
  ]

test_shadow = [
    shadow M.empty []               `satisfies` M.null,
    shadow M.empty ["x","y"]        `satisfies` M.null,
    shadow dummyEnv ["a"]           `is` dummyEnv, 
    shadow dummyEnv ["x","z"]       `is` (M.fromList [("y", makeTestValInt 1)]),
    shadow dummyEnv ["x","z", "a"]  `is` (M.fromList [("y", makeTestValInt 1)]),
    shadow dummyEnv ["x","z", "y"]  `satisfies` M.null
  ]

-- e[(x <- v)...]
substExpr :: M.Map Identifier Val -> Expr -> Expr
substExpr env (EArray a) = EArray $ substArray env a
substExpr env (EIden x)  =
  case M.lookup x env of
    Just v  -> EVal v
    Nothing -> EIden x
substExpr env (EApp es)  = EApp $ map (substExpr env) es
substExpr env (EUnbox x e e') = 
    EUnbox x (substExpr env e) (substExpr (shadow env [x]) e')
substExpr env (EVal v) = EVal $ substVal env v

substArray :: M.Map Identifier Val -> Array -> Array
substArray env (AArray (ls, ns)) = AArray (map (substArrayElement env) ls, ns)
substArray env (ABox e) = ABox (substExpr env e)

substArrayElement :: M.Map Identifier Val -> ArrayElement -> ArrayElement
substArrayElement env (ABase b) = ABase b
substArrayElement env (AFun f) = AFun (substFun env f)
substArrayElement env (AExpr e) = AExpr (substExpr env e)

substFun :: M.Map Identifier Val -> Fun -> Fun
substFun env (FPrim op) = FPrim op
substFun env (FLam binds e) = FLam binds (substExpr (shadow env (map getIden binds)) e)

substVal :: M.Map Identifier Val -> Val -> Val
substVal env (VBase b) = VBase b
substVal env (VFun f) = VFun (substFun env f)
substVal env (VBaseArray (ls, ns)) = VBaseArray (map (substVal env) ls, ns)
substVal env (VFunArray (ls, ns))  = VFunArray  (map (substVal env) ls, ns)
substVal env (VBox v) = VBox (substVal env v)
substVal env (VBoxArray (ls, ns))  = VBoxArray  (map (substVal env) ls, ns)

--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------

main :: IO ()
main = $(runTests)

