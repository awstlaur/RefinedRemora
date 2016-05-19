--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
---------------------------------- Remora.hs -----------------------------------
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------

{-# LANGUAGE DeriveGeneric #-}

module Remora where

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