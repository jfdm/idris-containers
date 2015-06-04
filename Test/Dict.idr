||| Testing Queues
module Test.Dict

import Test.Harness
import Data.AVL.Dict

partial
test2 : Test (List (Int, Int))
test2 = MkTest (Just "List, Building" )
               (Dict.toList $ Dict.fromList [(1,2), (2,3), (3,4)])
               [(1,2), (2,3), (3,4)]
               (==)


partial
test3 : Test (Maybe Int)
test3 = MkTest (Just "Lookup")
               (Dict.lookup 1 $ Dict.fromList [(1,2), (2,3), (3,4)])
               (Just 2)
               (==)

partial
test4 : Test (Dict Int Int)
test4 = MkTest (Just "Update")
               (Dict.remove 2 $ Dict.fromList [(1,2), (2,3), (3,4)])
               (Dict.fromList [(1,2), (3,4)])
               (==)

partial
test5 : Test (Dict Int Int)
test5 = MkTest (Just "Remove")
               (Dict.update 2 (*2) $ Dict.fromList [(1,2), (2,3), (3,4)])
               (Dict.fromList [(1,2), (2,6), (3,4)])
               (==)



partial
runTest : IO ()
runTest = do
  putStrLn "------------------------------------------------------------------------------"
  putStrLn "Testing Dict"
  runTests [
    testRunner test2
  , testRunner test3
  , testRunner test5
  , testRunner test4
  ]

-- --------------------------------------------------------------------- [ EOF ]
