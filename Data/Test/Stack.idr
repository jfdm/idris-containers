-- --------------------------------------------------------------- [ Stack.idr ]
-- Module    : Stack.idr
-- Copyright : (c) 2015,2016 See CONTRIBUTORS.md
-- License   : see LICENSE
-- --------------------------------------------------------------------- [ EOH ]
||| Testing Stacks using silly stupid tests
module Data.Test.Stack

import Test.Generic
import Data.Stack

%access export

covering
test2 : IO Bool
test2 = genericTest (Just "Pushing") (pushSThings [1,2,3] mkStack) [1,2,3] (==)

covering
test3 : IO Bool
test3 = genericTest (Just "Pushing Many") (pushSThings [1,2,3] (pushS 1 Nil)) [1,2,3,1] (==)

covering
test4 : IO Bool
test4 = genericTest (Just "Popping") (snd (popS [1,2,3]), fst (popS [1,2,3])) ([2,3],1) (==)

covering
runTest : IO ()
runTest = do
  putStrLn "Testing Stack"
  putStrLn infoLine
  NonReporting.runTests [
    genericTest (Just "Nothing") (the (Stack Nat) mkStack) (the (Stack Nat) Nil) (==)
  , test2
  , test3
  , test4
  ]

-- --------------------------------------------------------------------- [ EOF ]
