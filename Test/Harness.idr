module Test.Harness

import public System

data Test : Type -> Type where
  MkTest : (Show a) => (given : a) -> (expected : a) -> (a -> a -> Bool) -> String -> Test a

covering
testWrapper : (Show a) => String -> Test a -> IO (Maybe String)
testWrapper title (MkTest given expected test err) = do
    putStrLn $ unwords ["Begin Test:",title]
    if test given expected
      then pure Nothing
      else pure (Just $ unwords [
           "Error:"
         , err, "\n"
         , "Given:","\t"
         , show given, "\n"
         , "Expected:","\t"
         , show expected
         ])

covering
runTests : List (IO (Maybe String)) -> IO ()
runTests Nil     = putStrLn "All Tests have passed"
runTests (t::ts) =
  case !t of
    Nothing => do
      putStrLn $ "Test Passed"
      putStrLn "------------------------------------------------------------------------------"
      runTests ts
    Just err => do
      putStrLn "+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++-"
      putStrLn $ "Test Failed"
      putStrLn err
      putStrLn "+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++-"
      exit 1
