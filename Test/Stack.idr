||| Testing Stacks using silly stupid tests
module Test.Stack

import Test.Harness
import Data.Stack

covering
test2 : Test (Stack Nat)
test2 = MkTest (Just "Pushing") (pushSThings [1,2,3] mkStack) [1,2,3] (==)

covering
test3 : Test (Stack Nat)
test3 = MkTest (Just "Pushing Many") (pushSThings [1,2,3] (pushS 1 Nil)) [1,2,3,1] (==)

covering
test4 : Test (Stack Nat,Nat)
test4 = MkTest (Just "Popping") (snd (popS [1,2,3]), fst (popS [1,2,3])) ([2,3],1) (==)

covering
runTest : IO ()
runTest = do
  putStrLn "Testing Stack"
  putStrLn infoLine
  runTests [
    testRunner $ MkTest (Just "Nothing") (the (Stack Nat) mkStack) (the (Stack Nat) Nil) (==)
  , testRunner test2
  , testRunner test3
  , testRunner test4
  ]

-- --------------------------------------------------------------------- [ EOF ]
