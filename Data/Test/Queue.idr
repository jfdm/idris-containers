-- --------------------------------------------------------------- [ Queue.idr ]
-- Module    : Queue.idr
-- Copyright : (c) Jan de Muijnck-Hughes
-- License   : see LICENSE
-- --------------------------------------------------------------------- [ EOH ]
||| Testing Queues
module Data.Test.Queue

import Test.Generic
import Data.Queue

covering
test2 : IO ()
test2 = genericTest (Just "Enqueue") (pushQThings [1,2,3] mkQueue) (MkQ [3,2,1] Nil) (==)

partial
test3 : IO ()
test3 = genericTest (Just "Dequeue") (popQ (pushQThings [1,2,3] mkQueue)) (1,MkQ Nil [2,3]) (==)


partial
runTest : IO ()
runTest = do
  putStrLn "Testing Queue"
  putStrLn infoLine
  runTests [
    test2
  , test3
  ]

-- --------------------------------------------------------------------- [ EOF ]
