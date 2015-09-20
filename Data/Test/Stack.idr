||| Testing Stacks using silly stupid tests
module Data.Test.Stack

import Test.Generic
import Data.Stack

covering
test2 : IO ()
test2 = genericTest (Just "Pushing") (pushSThings [1,2,3] mkStack) [1,2,3] (==)

covering
test3 : IO ()
test3 = genericTest (Just "Pushing Many") (pushSThings [1,2,3] (pushS 1 Nil)) [1,2,3,1] (==)

covering
test4 : IO ()
test4 = genericTest (Just "Popping") (snd (popS [1,2,3]), fst (popS [1,2,3])) ([2,3],1) (==)

covering
runTest : IO ()
runTest = do
  putStrLn "Testing Stack"
  putStrLn infoLine
  runTests [
    genericTest (Just "Nothing") (the (Stack Nat) mkStack) (the (Stack Nat) Nil) (==)
  , test2
  , test3
  , test4
  ]

-- --------------------------------------------------------------------- [ EOF ]
