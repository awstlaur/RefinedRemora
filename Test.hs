{-# LANGUAGE TemplateHaskell #-}

module Test(
    is,
    raises,
    satisfies,
    runTests,
    testGroup
    )
where


import qualified Control.Exception as CE
import qualified Control.Monad as CM
import Language.Haskell.TH.Lib (ExpQ)

-- import Test.HUnit.Tools (assertRaises)
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.TH


infixl 8 `is`, `raises`

is :: (Eq a, Show a) => a -> a -> TestTree
actual `is` expected = testCase "" $ actual @?= expected

-- all "test_*" lists are interpreted as [TestTree] by tasty-th
test_is :: [TestTree]
test_is = [
    (True && False) `is` False, -- : OK
    True `is` False,            -- : FAIL
                                --   expected: False
                                --    but got: True
    div 1 0 `is` 0              -- : FAIL
                                --   Exception: divide by zero
  ]

raises :: (Show a, CE.Exception e, Show e, Eq e) => a -> e -> TestTree
x `raises` err = testCase "" $ assertRaises "" err $ CE.evaluate x

-- all "test_*" lists are interpreted as [TestTree] by tasty-th
test_raises = [
    div 1 0 `raises` CE.DivideByZero,    -- correct
    div 1 1 `raises` CE.DivideByZero,    -- incorrect: no exception raised
    div 1 0 `raises` CE.LossOfPrecision  -- incorrect: different exception raised
  ]

satisfies :: (Eq a, Show a) => a -> (a -> Bool) -> TestTree
actual `satisfies` predicate =
  let proposition = predicate actual
  in
    testCase "" $ proposition @? ("Does not satisfy!")

test_satisfies = [
    0 `satisfies` (== 0),      -- correct
    1 `satisfies` (== 0),      -- incorrect: does not satisfy
    div 1 0 `satisfies` (== 0) -- incorrect: exception raised
  ]

runTests :: ExpQ
runTests = defaultMainGenerator

-- copied and modified from testpack's Test.HUnit.Tools.assertRaises
-- hackage.haskell.org/package/testpack-2.1.3.0/docs/src/Test-HUnit-Tools.html#assertRaises
assertRaises :: (Show a, CE.Exception e, Show e, Eq e) =>
                String -> e -> IO a -> IO ()
assertRaises msg selector action =
    let thetest e = (CM.unless (e == selector) $
                     assertFailure $
                       msg ++
                         "Received unexpected exception: " ++
                           show e ++ "\ninstead of exception: " ++ show selector)
        in do
           r <- CE.try action
           case r of
                  Left e -> thetest e
                  Right _ -> assertFailure $ msg ++ "Received no exception, but was expecting exception: " ++ show selector

main :: IO ()
main = $(defaultMainGenerator)