||| Testing Queues
module Test.Dict

import Test.Harness
import Data.AVL.Dict

-- ------------------------------------------------------------ [ Construction ]
partial
testBuilding : Test (List (Int, Int))
testBuilding = MkTest
    (Just "List, Building" )
    (Dict.toList $ Dict.fromList [(1,2), (2,3), (3,4)])
    [(1,2), (2,3), (3,4)]
    (==)
-- ----------------------------------------------------------------- [ Removal ]
partial
testRemove : Test (Dict Int Int)
testRemove = MkTest
    (Just "Remove Existing Element")
    (Dict.remove 2 $ Dict.fromList [(1,2), (2,3), (3,4)])
    (Dict.fromList [(1,2), (3,4)])
    (==)

partial
testRemoveN : Test (Dict Int Int)
testRemoveN = MkTest
    (Just "Remove None Existing Element")
    (Dict.remove 7 $ Dict.fromList [(1,2), (2,3), (3,4)])
    (Dict.fromList [(1,2), (2,3), (3,4)])
    (==)

-- ---------------------------------------------------------------- [ Updating ]
partial
testUpdate : Test (Dict Int Int)
testUpdate = MkTest
    (Just "Update")
    (Dict.update 2 (*2) $ Dict.fromList [(1,2), (2,3), (3,4), (5,3)])
    (Dict.fromList [(1,2), (2,6), (3,4), (5,3)])
    (==)

partial
testMerge : Test (List (Int,Int))
testMerge = MkTest
    (Just "Merging")
    (Dict.toList $ Dict.merge
      (Dict.fromList [(1,2), (4,4)])
      (Dict.fromList [(2,4), (3,5), (5,6), (4,3), (4,2)]))
    ([(1,2), (2,4), (3,5), (4,2), (5,6)])
    (==)

partial
testHas : Test (Bool)
testHas = MkTest
   (Just "Has value")
   (hasValue 6 $ Dict.fromList [(1,2), (2,6), (3,4)])
   (True)
   (==)

-- ----------------------------------------------------------------- [ Queries ]
partial
testLookup : Test (Maybe Int)
testLookup = MkTest
    (Just "Lookup")
    (Dict.lookup 1 $ Dict.fromList [(1,2), (2,3), (3,4)])
    (Just 2)
    (==)

partial
testKVs : Test (List Int, List Int)
testKVs = MkTest
    (Just "KV Pair Extraction")
    (keys given, values given)
    ([1,2,3], [5,6,7])
    (==)
  where
    given : Dict Int Int
    given = Dict.fromList [(1,5), (2,6), (3,7)]

partial
runTest : IO ()
runTest = do
  putStrLn "Testing Dict"
  putStrLn infoLine
  runTests [
      testRunner testBuilding
    , testRunner testLookup
    , testRunner testUpdate
    , testRunner testRemove
    , testRunner testRemoveN
    , testRunner testMerge
    , testRunner testHas
    , testRunner testKVs
  ]

-- --------------------------------------------------------------------- [ EOF ]
