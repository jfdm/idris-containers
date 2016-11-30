-- ------------------------------------------------------------ [ RedBlack.idr ]
-- Module    : RedBlack.idr
-- Copyright : (c) 2015,2016 See CONTRIBUTORS.md
-- License   : see LICENSE
-- --------------------------------------------------------------------- [ EOH ]
||| Testing Stacks using silly stupid tests
module Data.Test.RedBlack

import Test.Generic
import Test.Random

import Data.RedBlack.Tree

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
    (Tree.size $ Tree.fromList (list1 ++ list1))
    30
    (==)


-- ---------------------------------------------------------------- [ Updating ]
partial
testUpdate : IO Bool
testUpdate = genericTest
    (Just "Insert")
    (Tree.size $ insert 1 $ Tree.fromList list2)
    31
    (==)

partial
testContains : IO Bool
testContains = genericTest
    (Just "Contains")
    (Tree.contains 4 $ Tree.fromList [1,2,3,4])
    (True)
    (==)

partial
runTest : IO ()
runTest = do
    putStrLn "Testing RedBlack Tree"
    putStrLn infoLine
    NonReporting.runTests [
        testBuilding
      , testUpdate
      , testContains
    ]

-- --------------------------------------------------------------------- [ EOF ]
