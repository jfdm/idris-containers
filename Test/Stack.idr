||| Testing Stacks using silly stupid tests
module Test.Stack

import Test.Harness
import Data.Stack


covering
test2 : Test (Stack Nat)
test2 = MkTest (pushSThings [1,2,3] mkStack) [1,2,3] (==) "Cannot push"

covering
test3 : Test (Stack Nat)
test3 = MkTest (pushSThings [1,2,3] (pushS 1 Nil)) [1,2,3,1] (==) "Pushing hard"

covering
test4 : Test (Stack Nat,Nat)
test4 = MkTest (snd (popS [1,2,3]), fst (popS [1,2,3])) ([2,3],1) (==) "Pop"

covering
runTest : IO ()
runTest = do
  putStrLn "------------------------------------------------------------------------------"
  putStrLn "Testing Stack"
  runTests [
    testWrapper "Round 1" $ MkTest (the (Stack Nat) mkStack) (the (Stack Nat) Nil) (==) "No Empty"
  , testWrapper "Round 2" test2
  , testWrapper "Round 3" test3
  , testWrapper "Round 4" test4
  ]

-- --------------------------------------------------------------------- [ EOF ]
