||| Testing Stacks using silly stupid tests
module Test.RedBlack.Tree

import Test.Harness
import Test.Random

import Data.RedBlack.Tree


list1 : List Integer
list1 = genRndListU 123456789 (0,100) 30

list2 : List Integer
list2 = genRndListU 987654321 (0,100) 30

-- ------------------------------------------------------------ [ Construction ]
partial
testBuilding : Test Nat
testBuilding = MkTest
    (Just "List, Building" )
    (Tree.size $ Tree.fromList (list1 ++ list1))
    30
    (==)


-- ---------------------------------------------------------------- [ Updating ]
partial
testUpdate : Test Nat
testUpdate = MkTest
    (Just "Insert")
    (Tree.size $ insert 1 $ Tree.fromList list2)
    31
    (==)

partial
testContains : Test Bool
testContains = MkTest
    (Just "Contains")
    (Tree.contains 4 $ Tree.fromList [1,2,3,4])
    (True)
    (==)

partial
runTest : IO ()
runTest = do
    putStrLn "Testing RedBlack Tree"
    putStrLn infoLine
    runTests [
        testRunner testBuilding
      , testRunner testUpdate
      , testRunner testContains
    ]

-- --------------------------------------------------------------------- [ EOF ]
