module Test.Harness

import public System

fancyLine : Nat -> Char -> String
fancyLine l c = pack $ replicate l c

infoLine : String
infoLine = fancyLine 40 '-'

succLine : String
succLine = fancyLine 40 '='

errLine : String
errLine = fancyLine 40 '+'

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
              , fromMaybe "Unnamed Test" title
              ]
    if test given expected
      then pure ()
      else with List do
         putStrLn $ unwords [
               errLine
             , "\n"
             , "Error:\n\n"
             , "Given:\n\t"
             , show given
             , "\n"
             , "Expected:\n\t"
             , show expected
             , "\n"
             , errLine
             , "\n"
             ]
         exit 1

covering
runTests : List (IO ()) -> IO ()
runTests Nil     = do putStrLn "All Tests have passed"; putStrLn succLine
runTests (t::ts) = do t; runTests ts
