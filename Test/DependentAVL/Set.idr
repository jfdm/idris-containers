||| Testing Stacks using silly stupid tests
module Test.DependentAVL.Set

import Test.Harness
import Test.Random

import Data.AVL.Dependent.Set

list1 : List Integer
list1 = genRndList 123456789 (0,100) 30

list2 : List Integer
list2 = genRndList 987654321 (0,100) 30


set1' : Set Integer
set1' = Set.insert 101 $ Set.fromList list1

set1 : Set Integer
set1 = Set.fromList list1

set2 : Set Integer
set2 = Set.fromList list2


-- ------------------------------------------------------------ [ Construction ]
partial
testBuilding : Test (Bool)
testBuilding = MkTest
    (Just "List, Building" )
    (sorted $ Set.toList $ Set.fromList list1)
    True
    (==)


-- ---------------------------------------------------------------- [ Updating ]

partial
testUpdate : Test (Bool)
testUpdate = MkTest
    (Just "Insert")
    (Set.size set1' == 31 && Set.size set1 == 30)
    True
    (==)


partial
testMerge : Test (Nat)
testMerge = MkTest
    (Just "Union")
    (Set.size $ Set.union set1 set2)
    (60)
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
    (Set.contains 4 $ Set.fromList [4,3,7,3,8,5,2,6,3])
    (True)
    (==)

partial
runTest : IO ()
runTest = do
    putStrLn "Testing Set"
    putStrLn infoLine
    runTests [
        testRunner testBuilding
      , testRunner testUpdate
      , testRunner testMerge
      , testRunner testContains
      , testRunner testDiff
      , testRunner testIntersection
    ]

-- --------------------------------------------------------------------- [ EOF ]
