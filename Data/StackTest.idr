||| Testing Stacks using sill stupid tests
module Data.Stack.Test

import System
import Data.Stack

||| Test Runner
doTest : (Show a) => String -> Stack a -> Stack a -> IO ()
doTest title given expected = do
  putStrLn title
  case show given == show expected of
    True =>  putStrLn "Test Passed"
    False => do
      putStr "Given: "
      printLn given
      putStr "Expected: "
      printLn expected
      exit 1

runTest : IO ()
runTest = do
  doTest "Round 1" (the (Stack Nat) mkStack) (the (Stack Nat) Nil)
  doTest "Round 2" (pushSThings [1,2,3] mkStack) [1,2,3]
  doTest "Round 3" (pushSThings [1,2,3] (pushS 1 Nil)) [1,2,3,1]
  doTest "Round 4" (snd $ popS [1,2,3]) ([2,3])
  doTest "Round 5" ([fst $ popS [1,2,3]]) ([1])


-- --------------------------------------------------------------------- [ EOF ]
