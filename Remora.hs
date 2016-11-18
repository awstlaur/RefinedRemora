--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
---------------------------------- Remora.hs -----------------------------------
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------

{-# LANGUAGE DeriveGeneric #-}

module Remora where

-- import Data.List.NonEmpty
import Text.PrettyPrint.GenericPretty

type Identifier = String
type Nat = Int -- I know, I know

data R_Index =
      R_ILit Nat
    | R_IIden Identifier
    | R_IShape [R_Index]
    | R_IPlus R_Index R_Index
    deriving (Eq, Generic)
instance Out R_Index

data R_Sort =
      R_SNat
    | R_SShape
    deriving (Eq, Generic)
instance Out R_Sort

data R_BaseType =
      R_BTBool
    | R_BTNum
    deriving (Eq, Generic)
instance Out  R_BaseType

type R_IdenSortBinding = (Identifier, R_Sort)

data R_Type =
      R_TBase R_BaseType
    | R_TVar Identifier
    | R_TArray R_Index R_Type
    | R_TArrow [R_Type] R_Type
    | R_TUniv [Identifier] R_Type
    | R_TDepProd [R_IdenSortBinding] R_Type
    | R_TDepSum [R_IdenSortBinding] R_Type
    deriving (Eq, Generic)
instance Out R_Type

r_TNum :: R_Type
r_TNum = R_TBase R_BTNum

r_TBool :: R_Type
r_TBool = R_TBase R_BTBool

type R_IdenTypeBinding = (Identifier, R_Type)

data R_Base = 
      R_BInt Int
    | R_BBool Bool

data R_PrimOp =
      R_PIntToInt (Int -> Int)
    | R_PIntToBool (Int -> Bool)
    | R_PBoolToInt (Bool -> Int)
    | R_PBoolToBool (Bool -> Bool)

data R_Expr =
      R_EArray R_Array
    | R_EIden Identifier
    | R_EApp [R_Expr] -- non-empty
    | R_ETLam [Identifier] R_Expr
    | R_ETApp R_Expr [R_Type]
    | R_EILam [R_IdenSortBinding] R_Expr
    | R_EIApp R_Expr [R_Sort]
    | R_EPack [R_Index] R_Expr R_Type
    | R_EUnpack [Identifier] Identifier R_Expr R_Expr

data R_Array =
      R_ATyped [R_ArrayElement] R_Type
    | R_AIndexed [R_ArrayElement] R_Index -- non-empty

data R_ArrayElement =
      R_ABase R_Base
    | R_AFun R_Fun
    | R_AExpr R_Expr
    | R_ATLam [Identifier] R_ArrayElement
    | R_ATApp R_ArrayElement [R_Type]
    | R_AILam [R_IdenSortBinding] R_ArrayElement
    | R_AIApp R_ArrayElement [R_Sort]

data R_Fun =
      R_FPrimtive R_PrimOp
    | R_FLambda [R_IdenTypeBinding] R_Expr

type R_VPackData = ([R_Index], R_Value)

data R_Value =
      R_VArrayOfBase [R_Base] R_Type
    | R_VArrayOfFun [R_Fun] R_Type
    | R_VBase R_Base
    | R_VFun R_Fun
    | R_VTLam [Identifier] R_ArrayElement
    | R_VILam [R_IdenSortBinding] R_ArrayElement
    | R_VPack R_VPackData
    | R_VPackArray [R_VPackData] R_Type -- (type must be A_{S m n ...}^{\tau})


toArrayElement :: R_Expr -> Maybe R_ArrayElement
toArrayElement (R_ETLam xs e) = (toArrayElement e) >>= (\l -> Just (R_ATLam xs l))
toArrayElement (R_ETApp e taus) = (toArrayElement e) >>= (\l -> Just (R_ATApp l taus))
toArrayElement (R_EILam binds e) = (toArrayElement e) >>= (\l -> Just (R_AILam binds l))
toArrayElement (R_EIApp e iotas) = (toArrayElement e) >>= (\l -> Just (R_AIApp l iotas))
toArrayElement e = Just . R_AExpr $ e

-- 
toVal :: R_Expr -> Maybe R_Value
toVal (R_EArray alpha) = arrayToVal alpha
toVal (R_EIden iden) = Nothing
toVal (R_EApp es) = Nothing
toVal (R_ETLam xs e) = arrayElementToVal e
toVal (R_ETApp e taus) = Nothing
toVal (R_EILam binds e) = arrayElementToVal e
toVal (R_EIApp e iotas) = Nothing
toVal (R_EPack iotas e tau) = toVal e
toVal (R_EUnpack xs y e e') = Nothing

arrayElementsToVal :: [R_ArrayElement] -> Maybe R_Value
arrayElementsToVal ls

arrayToVal :: R_Array -> Maybe R_Value
arrayToVal (R_ATyped   ls tau)  = 
arrayToVal (R_AIndexed ls iota) | (length ls > 0) =
arrayToVal _ = Nothing

arrayElementToBaseVal (R_ABase b) = Just . R_VBase $ b
arrayElementToBaseVal _           = Nothing

arrayElementToFunVal  (R_AFun  f) = Just . R_VFun  $ f
arrayElementToFunVal  _           = Nothing

arrayElementToPackVal (R_AExpr (R_EPack iotas e tau)) = (toVal e) >>= 

arrayElementToVal :: R_ArrayElement -> Maybe R_Value
arrayElementToVal (R_ABase b)        = arrayElementToBaseVal (R_ABase b)
arrayElementToVal (R_AFun  f)        = arrayElementToFunVal  (R_AFun  f)
arrayElementToVal (R_AExpr e)        =
  case e of
    | R_EPack iotas e' tau =>
      case (toVal e') of
        Just v  => Just . R_VPack $ (iotas, v)
        Nothing => Nothing
    | _                    => Nothing
arrayElementToVal (R_ATLam xs l')    = R_VTLam xs l'
arrayElementToVal (R_AILam binds l') = R_VILam binds l'
arrayElementToVal _                  = Nothing

-- http://stackoverflow.com/a/17253034
lastN n xs = drop (length xs - n) xs

-- http://stackoverflow.com/a/8681226
splitEvery _ [] = []
splitEvery n list = first : (splitEvery n rest)
  where
    (first,rest) = splitAt n list

-- Cells (Fig. 5)
cells :: Nat -> [a] -> [Nat] -> [[a]]
cells n ls ns =
    let m = product (lastN n ns)
    in splitEvery m ls

-- TODO: Fig. 9
smallStep :: R_Expr -> Maybe R_Expr
smallStep _ = Nothing
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
---------------------------------- JUDGMENT ------------------------------------
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------

-- \Theta |- \iota :: \gamma
sortCheck :: [R_IdenSortBinding] -> R_Index -> R_Sort -> Bool
sortCheck theta (R_ILit n) R_SNat = True                            -- (S-Nat)
sortCheck theta (R_IIden iden) gamma = elem (iden, gamma) theta     -- (S-Var)
sortCheck theta (R_IShape idxs) R_SShape =
    and $ map (\idx -> sortCheck theta idx R_SNat) idxs             -- (S-Shape)
sortCheck theta (R_IPlus idx0 idx1) R_SNat =
    sortCheck theta (R_IShape [idx0, idx1]) R_SShape                -- (S-Plus)
sortCheck _ _ _ = False                                             -- failure  

-- \Delta, \Theta |- \tau
kindCheck :: [Identifier] -> [R_IdenSortBinding] -> R_Type -> Bool
kindCheck delta theta (R_TBase _) = True                            -- (K-Base)
kindCheck delta theta (R_TVar iden) = elem iden delta               -- (K-Var)
kindCheck delta theta (R_TArray idx rtype) =
    and [kindCheck delta theta rtype, sortCheck theta idx R_SShape] -- (K-Array)
kindCheck delta theta (R_TArrow args ret) =
    and $ map (kindCheck delta theta) (args ++ [ret])               -- (K-Fun)
kindCheck delta theta (R_TDepProd binds rtype) =
    kindCheck delta (theta ++ binds) rtype                          -- (K-DProd)
kindCheck delta theta (R_TDepSum binds rtype) =
    kindCheck delta (theta ++ binds) rtype                          -- (K-DSum)
kindCheck delta theta (R_TUniv idens rtype) =
    kindCheck (delta ++ idens) theta rtype                          -- (K-Univ)

sortCheckEmptyEnv :: R_Index -> R_Sort -> Bool
sortCheckEmptyEnv iota gamma = sortCheck [] iota gamma

kindCheckEmptyEnv :: R_Type -> Bool
kindCheckEmptyEnv tau = kindCheck [] [] tau

--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
---------------------------------- EXAMPLES ------------------------------------
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------

failSortCheck :: R_Index
failSortCheck = R_IShape [(R_IShape [R_ILit 2])]

-- type with free var is not well formed
failKindCheck = (R_TArray (R_IShape [(R_IIden "n")]) (R_TBase R_BTBool))

-- A_{(S n m t)}\tau
ex0 :: R_Type
ex0 = R_TUniv ["tau"]
    (R_TDepProd [("m", R_SNat), ("n", R_SNat), ("t", R_SNat)]
        (R_TArray
                    (R_IShape [(R_IIden "n"), (R_IIden "m"), (R_IIden "t")])
                    (R_TVar "tau")))

-- append
-- (A_{(S m)}A_{d}t, A_{(S n)}A_{d}t -> A_{(S (+ m n))}A_{d}t)
appendType :: R_Type
appendType = R_TUniv ["t"]
    (R_TDepProd [("m", R_SNat), ("n", R_SNat), ("d", R_SShape)]
        (R_TArrow [
                      R_TArray (R_IShape [R_IIden "m"]) (R_TArray (R_IIden "d") (R_TVar "t"))
                    , R_TArray (R_IShape [R_IIden "n"]) (R_TArray (R_IIden "d") (R_TVar "t"))
                    ]
                 (R_TArray (R_IShape [(R_IPlus (R_IIden "m") (R_IIden "n"))])
                    (R_TArray (R_IIden "d") (R_TVar "t"))))
    )

-- iota
-- A_{(S m)}Num -> \Sigma [(d Shape)] A_{d}Num
iotaType :: R_Type
iotaType = R_TDepProd [("n", R_SNat)]
    (R_TArrow [R_TArray (R_IShape [R_IIden "n"]) r_TNum]
        (R_TDepSum [("d", R_SShape)] (R_TArray (R_IIden "d") r_TNum)))