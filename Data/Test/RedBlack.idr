-- ------------------------------------------------------------ [ RedBlack.idr ]
-- Module    : RedBlack.idr
-- Copyright : (c) 2015,2016 See CONTRIBUTORS.md
-- License   : see LICENSE
-- --------------------------------------------------------------------- [ EOH ]
||| Testing Stacks using silly stupid tests
module Data.Test.RedBlack

import Test.Unit
import Test.Random.Values

import Data.RedBlack.BTree

%access export

list1 : List Integer
list1 = rndListIntU 123456789 (0,100) 30

list2 : List Integer
list2 = rndListIntU 987654321 (0,100) 30

-- ------------------------------------------------------------ [ Construction ]
partial
testBuilding : IO Bool
testBuilding = genericTest
    (Just "List, Building" )
    (BTree.size $ BTree.fromList (list1 ++ list1))
    30
    (==)


-- ---------------------------------------------------------------- [ Updating ]
partial
testUpdate : IO Bool
testUpdate = genericTest
    (Just "Insert")
    (BTree.size $ insert 1 $ BTree.fromList list2)
    31
    (==)

partial
testContains : IO Bool
testContains = genericTest
    (Just "Contains")
    (BTree.contains 4 $ BTree.fromList [1,2,3,4])
    (True)
    (==)

partial
runTest : IO ()
runTest = do
    putStrLn "Testing RedBlack BTree"
    putStrLn infoLine
    NonReporting.runTests [
        testBuilding
      , testUpdate
      , testContains
    ]

-- --------------------------------------------------------------------- [ EOF ]
