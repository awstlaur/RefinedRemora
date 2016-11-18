--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
------------------------------ RefinedRemora.hs --------------------------------
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------

{-# LANGUAGE DeriveGeneric #-}

import qualified Remora as RM
import Text.PrettyPrint.GenericPretty

-- For the pretty printer --
instance Out IntBinop
instance Out IntUnop
instance Out BoolBinopOfInt
instance Out BoolBinop
instance Out BoolUnop
instance Out IntIndex
instance Out BoolIndex
instance Out Index
instance Out RSort
instance Out BaseType
instance Out RType

-- at the repl, use `pp <identifier>` to invoke the pretty printer

--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
------------------------------- TYPES AND DATA ---------------------------------
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------

type Identifier = String
type IdenSortBinding = (Identifier, RSort)
type IdenListSortBinding = ([Identifier], RSort)

data IntBinop =
      IPlus
    | ISub
    | IMult
    | IDiv
    | IMin
    | IMax
    | IRem
    deriving (Eq, Generic, Show)

data IntUnop =
      IAbs
    | ISgn
    deriving (Eq, Generic, Show)

data BoolBinopOfInt =
      BLt
    | BEq
    | BGt
    deriving (Eq, Generic, Show)

data BoolBinop =
      BAnd
    | BOr
    deriving (Eq, Generic, Show)

data BoolUnop =
    BNot
    deriving (Eq, Generic, Show)

data IntIndex =
      IIden Identifier
    | ILit Int
    | IBinop IntBinop IntIndex IntIndex
    | IUnop IntUnop IntIndex
    deriving (Eq, Generic, Show)

data BoolIndex =
      BIden Identifier
    | BLit Bool
    | BBinopOfInt BoolBinopOfInt IntIndex IntIndex
    | BBinop BoolBinop BoolIndex BoolIndex
    | BUnop BoolUnop BoolIndex
    deriving (Eq, Generic, Show)

data Index =
      IBool BoolIndex
    | IInt  IntIndex
    | IShape [IntIndex]
    deriving (Eq, Generic, Show)

data RSort =
      SInt
    | SBool
    | SShape
    | SRefine [IdenSortBinding] [BoolIndex]
    | SNatSugar
    deriving (Eq, Generic, Show)

data BaseType =
      BTBool
    | BTInt
    | BTArray
    deriving (Eq, Generic, Show)

data RType =
      TVar Identifier
    | TBase BaseType [Index] [RType]
    | TArrow [RType] RType
    | TUniv [Identifier] RType
    | TDepProd [IdenListSortBinding] RType
    | TDepSum [IdenListSortBinding] RType
    deriving (Eq, Generic, Show)

desugarSort :: RSort -> RSort
desugarSort (SRefine binds bIdxs) =
    SRefine (map (\(iden,rsort) -> (iden, desugarSort rsort)) binds) bIdxs
desugarSort SNatSugar = natSort
desugarSort x = x

tBool :: RType
tBool = TBase BTBool [] []

tInt :: RType
tInt = TBase BTInt [] []

tArray :: [Index] -> RType -> RType
tArray idxs rtype = TBase BTArray idxs [rtype]

--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
--------------------- Remora Types -> RefinedRemora Types ----------------------
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------


convert :: RM.R_Type -> RType 
convert (RM.R_TBase base) = TBase (convertBT base) [] []
convert (RM.R_TVar iden)  = TVar iden
convert (RM.R_TArray idx rtype) = tArray (convertIdx idx) (convert rtype)
convert (RM.R_TArrow args ret) = TArrow (map convert args) (convert ret)
convert (RM.R_TUniv idens rtype) = TUniv idens (convert rtype)
convert (RM.R_TDepProd binds rtype) = TDepProd (map convertBind binds) (convert rtype)
convert (RM.R_TDepSum binds rtype) = TDepSum (map convertBind binds) (convert rtype)

convertBind :: RM.R_IdenSortBinding -> IdenListSortBinding
convertBind (iden, rsort) = ([iden], convertDesugarSort rsort)

convertSort :: RM.R_Sort -> RSort
convertSort RM.R_SNat = SNatSugar
convertSort RM.R_SShape = SShape

convertDesugarSort :: RM.R_Sort -> RSort
convertDesugarSort = desugarSort . convertSort

convertBT :: RM.R_BaseType -> BaseType
convertBT RM.R_BTBool = BTBool
convertBT RM.R_BTNum = BTInt

convertIdx :: RM.R_Index -> [Index]
convertIdx (RM.R_IShape idxs) = map (IInt . convertIntIdx) idxs
convertIdx idx = [(IInt . convertIntIdx) idx]

convertIntIdx :: RM.R_Index -> IntIndex
convertIntIdx (RM.R_ILit x) = ILit x
convertIntIdx (RM.R_IIden iden) = IIden iden
convertIntIdx (RM.R_IPlus idx0 idx1) =
    IBinop IPlus (convertIntIdx idx0) (convertIntIdx idx1)

--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
---------------------------------- JUDGMENT ------------------------------------
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------

checkSInt  theta = (\idx -> sortCheck theta (IInt  idx) SInt)
checkSBool theta = (\idx -> sortCheck theta (IBool idx) SBool)

-- \Theta |- \iota :: \gamma
sortCheck :: [IdenSortBinding] -> Index -> RSort -> Bool
sortCheck theta (IInt (IIden x)) gamma  = elem (x, gamma) theta  -- (S-Var)
sortCheck theta (IBool (BIden x)) gamma = elem (x, gamma) theta  -- (S-Var)

sortCheck theta (IInt idx) SInt = case idx of
    ILit n -> True -- (S-Int)
    IBinop _ idx0 idx1 -> (checkSInt theta idx0) && (checkSInt theta idx1) -- (S-IntBinop)
    IUnop _ idx0 -> checkSInt theta idx0 -- (S-IntUnop)
    _ -> False -- failure

sortCheck theta (IBool idx) SBool = case idx of
    BLit b  -> True -- (S-Bool)
    BBinopOfInt _ idx0 idx1 -> (checkSInt theta idx0)  && (checkSInt theta idx1)  -- (S-BoolBinopOfInt)
    BBinop      _ idx0 idx1 -> (checkSBool theta idx0) && (checkSBool theta idx1) -- (S-BoolBinop)
    BUnop _ idx0 -> checkSBool theta idx0 -- (S-BoolUnop)
    _ -> False -- failure

sortCheck theta (IShape intIdxs) SShape =
    and $ map (checkSInt theta) intIdxs -- (S-Shape)

sortCheck _ _ _ = False -- failure

-- \Delta, \Theta |- \tau
kindCheck :: [Identifier] -> [IdenSortBinding] -> RType -> Bool
kindCheck delta theta tau = True


--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
------------------------------------ UTILS -------------------------------------
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------

natIndex :: IntIndex -> BoolIndex
natIndex idx =
    (BBinop BOr 
            (BBinopOfInt BGt idx (ILit 0))
            (BBinopOfInt BEq idx (ILit 0)))

makeNatSort :: Identifier -> RSort
makeNatSort iden = SRefine [(iden, SInt)] $ [natIndex $ IIden iden]

natSort :: RSort
natSort = makeNatSort "__n"

bindToNat :: [Identifier] -> [IntIndex] -> RSort
bindToNat idens shape =
    desugarSort (SRefine (map (\id -> (id, SNatSugar)) idens) [])

bindToNat' :: [Identifier] -> [IntIndex] -> RSort
bindToNat' idens shape =
    desugarSort (SRefine (map (\id -> (id, SInt)) idens) (map natIndex shape))


-- \forall\tau . \Pi binds . A_{shape}\tau
arrTypePoly :: Identifier -> [IdenListSortBinding] -> [IntIndex] -> RType
arrTypePoly tau binds shape =
    (TUniv [tau] (TDepProd binds (tArray (map IInt shape) (TVar tau))))

arrTypeShapely :: [Identifier] -> [IntIndex] -> RType
arrTypeShapely idens shape =
    (arrTypePoly "tau" [(idens, bindToNat' idens shape)] shape)

arrTypePlain :: [Identifier] -> RType
arrTypePlain idens = arrTypeShapely idens shape
    where shape = (map IIden idens)


--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
---------------------------------- EXAMPLES ------------------------------------
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------


-- A_{(S n m t)}\tau
ex0 :: RType
ex0 = arrTypePlain ["n", "m", "t"]


--A_{(S
--    (+ n m)
--    (- m t)
--    (rem m 2)
--    (min n 1)
--)}\tau

ex1Shape :: [IntIndex]
ex1Shape =
    [   (IBinop IPlus (IIden "n") (IIden "m"))
      , (IBinop ISub  (IIden "m") (IIden "t"))
      , (IBinop IRem  (IIden "m") (ILit   2))
      , (IBinop IMin  (IIden "n") (ILit   1))
    ]

ex1Refinement :: RSort
ex1Refinement =
    SRefine [("n", SInt),("m", SInt),("t", SInt)] (map natIndex ex1Shape)
        
ex1 :: RType
ex1 = arrTypeShapely ["n", "m", "t"] ex1Shape


-- An array A_{(S a b c)}Int s.t. a = b = c
-- all of whose entries are the same number ("x")
-- watch out for shadowing! in the array,
-- a is not necessarily equal to x
-- However, when checking the refinement, subst [x <- a, y <- b, z <- c]
ex2 :: RType
ex2 =
    TUniv ["tau"]
          (TDepProd [(["a","b","c"],
                      SRefine [("x", SInt),("y", SInt),("z", SInt)]
                              [BBinopOfInt BEq (IIden "x") (IIden "y"),
                               BBinopOfInt BEq (IIden "y") (IIden "z"),
                               BBinopOfInt BGt (IIden "x") (ILit 0)]),
                     (["x"], SInt)]
                    (TBase BTArray
                           [IInt (IIden "a"),IInt (IIden "b"),IInt (IIden "c")]
                           [TBase BTInt [IInt (IIden "x")] []]))




-- arithmetic binops:
-- (A_{(S)}Int  A_{(S)}Int -> A_{(S)}Int)

emptyShapeInt = TBase BTArray [] [tInt]

arithBinopType :: RType
arithBinopType = TArrow [emptyShapeInt, emptyShapeInt] emptyShapeInt

-- head:
-- forall t, Pi[(n Nat) (d Shape)]
--     (A_{(S (+ 1 n))}A_{d}t -> A_{d}t)

--headType :: RType
--headType = TUniv ["tau"] $ TDepProd [("n", natSort), ("d", SShape)]
--    (TArrow (arrTypeShapely ["n"] [IPlus (ILit 1) (IIden "n")])