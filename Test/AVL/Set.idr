||| Testing Stacks using silly stupid tests
module Test.AVL.Set

import Test.Harness
import Test.Random

import Data.AVL.Set

list1 : List Integer
list1 = genRndListU 123456789 (0,100) 30

list2 : List Integer
list2 = genRndListU 987654321 (101,200) 30


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
    (Set.size set1 == 30 && (sorted $ Set.toList $ Set.fromList list1))
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
testDiff : Test Nat
testDiff = MkTest
   (Just "Difference")
   (Set.size $ Set.difference set1 set1)
   30
   (==)

partial
testIntersection : Test (Nat)
testIntersection = MkTest
    (Just "Intersection")
    (Set.size $ Set.intersection set1 set1)
    30
    (==)

partial
testContains : Test Bool
testContains = MkTest
    (Just "Contains")
    (Set.contains 102 $ set1)
    (False)
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
