||| Testing Sets
module Test.Set

import Test.Harness
import Data.AVL.Set

-- ------------------------------------------------------------ [ Construction ]
partial
testBuilding : Test (List Int)
testBuilding = MkTest
    (Just "List, Building" )
    (Set.toList $ Set.fromList [1,2,3,4,4,5,6])
    [1,2,3,4,5,6]
    (==)
-- ----------------------------------------------------------------- [ Removal ]
partial
testRemove : Test (List Int)
testRemove = MkTest
    (Just "Remove Existing Element")
    (Set.toList $ Set.delete 2 $ Set.fromList [1,2,3,4,5,5,6])
    [1,3,4,5,6]
    (==)

-- ---------------------------------------------------------------- [ Updating ]
partial
testUpdate : Test (List Int)
testUpdate = MkTest
    (Just "Insert")
    (Set.toList $ Set.insert 1 $ Set.fromList [2,3,4,5])
    [1,2,3,4,5]
    (==)

partial
testMerge : Test (List Int)
testMerge = MkTest
    (Just "Union")
    (Set.toList $ Set.union
      (Set.fromList [1,4])
      (Set.fromList [2,3,5,4,3]))
    [1,2,3,4,5]
    (==)

partial
testDiff : Test (List Int)
testDiff = MkTest
   (Just "Difference")
   (Set.toList $ Set.difference
     (Set.fromList [2,4,6,8,9,1008])
     (Set.fromList [4,2,4,6,8,1006,5,78,34]))
   [2,4,6,8]
   (==)

partial
testIntersection : Test (List Int)
testIntersection = MkTest
    (Just "Intersection")
    (Set.toList $ Set.intersection
        (Set.fromList [1,2,3,4,5,6,7,8,9])
        (Set.fromList [1,2,33,44,55,66,77,88,99]))
    [1,2]
    (==)

partial
testContains : Test Bool
testContains = MkTest
    (Just "Contains")
    (Set.contains 4 $ Set.fromList [1,2,3,4])
    (True)
    (==)

partial
runTest : IO ()
runTest = do
    putStrLn "Testing Set"
    putStrLn infoLine
    runTests [
        testRunner testBuilding
      , testRunner testRemove
      , testRunner testUpdate
      , testRunner testMerge
      , testRunner testDiff
      , testRunner testIntersection
      , testRunner testContains
    ]

-- --------------------------------------------------------------------- [ EOF ]
