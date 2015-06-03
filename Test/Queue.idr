||| Testing Queues
module Test.Queue

import Test.Harness
import Data.Queue

covering
test2 : Test (Queue Nat)
test2 = MkTest (pushQThings [1,2,3] mkQueue) (MkQ [3,2,1] Nil) (==) "Enqueue"

partial
test3 : Test (Nat, Queue Nat)
test3 = MkTest (popQ (pushQThings [1,2,3] mkQueue)) (1,MkQ Nil [2,3]) (==) "Pop"


partial
runTest : IO ()
runTest = do
  putStrLn "------------------------------------------------------------------------------"
  putStrLn "Testing Queue"
  runTests [
    testWrapper "Round 1" test2
  , testWrapper "Round 2" test3
  ]

-- --------------------------------------------------------------------- [ EOF ]
