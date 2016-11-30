-- --------------------------------------------------------------- [ Queue.idr ]
-- Module    : Queue.idr
-- Copyright : (c) 2015,2016 See CONTRIBUTORS.md
-- License   : see LICENSE
-- --------------------------------------------------------------------- [ EOH ]
||| Testing Queues
module Data.Test.Queue

import Test.Generic
import Data.Queue

%access export

covering
test2 : IO Bool
test2 = genericTest (Just "Enqueue") (pushQThings [1,2,3] mkQueue) (pushQ 3 $ pushQ 2 $ pushQ 1 mkQueue) (==)

partial
test3 : IO Bool
test3 = genericTest (Just "Dequeue") (popQ' (pushQThings [1,2,3] mkQueue)) (Just (1, pushQThings [2,3] mkQueue)) (==)


partial
runTest : IO ()
runTest = do
  putStrLn "Testing Queue"
  putStrLn infoLine
  NonReporting.runTests [
    test2
  , test3
  ]

-- --------------------------------------------------------------------- [ EOF ]
