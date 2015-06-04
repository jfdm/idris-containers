module Test.Harness

import public System

data Test : Type -> Type where
  MkTest : (Show a) => Maybe String
                   -> (given : a)
                   -> (expected : a)
                   -> (a -> a -> Bool)
                   -> Test a

covering
testRunner : (Show a) => Test a -> IO ()
testRunner (MkTest title given expected test) = do
    putStrLn $ unwords [
               "Begin Test:"
              , fromMaybe "" title
              , if isJust title then "\n" else ""]
    if test given expected
      then pure ()
      else with List do
         putStrLn $ unwords [
               "++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++","\n"
             , "Error:", "\n"
             , "Given:","\t"
             , show given, "\n"
             , "Expected:","\t"
             , show expected
             , "++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++","\n"
             ]
         exit 1

covering
runTests : List (IO ()) -> IO ()
runTests Nil     = do putStrLn "All Tests have passed"
runTests (t::ts) = do t; runTests ts
