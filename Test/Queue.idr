||| Testing Queues
module Test.Queue

import Test.Harness
import Data.Queue

covering
test2 : Test (Queue Nat)
test2 = MkTest (Just "Enqueue") (pushQThings [1,2,3] mkQueue) (MkQ [3,2,1] Nil) (==)

partial
test3 : Test (Nat, Queue Nat)
test3 = MkTest (Just "Dequeue") (popQ (pushQThings [1,2,3] mkQueue)) (1,MkQ Nil [2,3]) (==)


partial
runTest : IO ()
runTest = do
  putStrLn "------------------------------------------------------------------------------"
  putStrLn "Testing Queue"
  runTests [
    testRunner test2
  , testRunner test3
  ]

-- --------------------------------------------------------------------- [ EOF ]
