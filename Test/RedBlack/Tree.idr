||| Testing Stacks using silly stupid tests
module Test.RedBlack.Tree

import Test.Harness
import Data.RedBlack.Tree

-- ------------------------------------------------------------ [ Construction ]
partial
testBuilding : Test (List Int)
testBuilding = MkTest
    (Just "List, Building" )
    (Tree.toList $ Tree.fromList [1,2,3,4,4,5,6])
    [1,2,3,4,5,6]
    (==)


-- ---------------------------------------------------------------- [ Updating ]
partial
testUpdate : Test (List Int)
testUpdate = MkTest
    (Just "Insert")
    (Tree.toList $ Tree.insert 1 $ Tree.fromList [2,3,4,5])
    [1,2,3,4,5]
    (==)

-- partial
-- testMerge : Test (List Int)
-- testMerge = MkTest
--     (Just "Union")
--     (Tree.toList $ Tree.union
--       (Tree.fromList [1,4])
--       (Tree.fromList [2,3,5,4,3]))
--     [1,2,3,4,5]
--     (==)

-- partial
-- testDiff : Test (List Int)
-- testDiff = MkTest
--    (Just "Difference")
--    (Tree.toList $ Tree.difference
--      (Tree.fromList [2,4,6,8,9,1008])
--      (Tree.fromList [4,2,4,6,8,1006,5,78,34]))
--    [2,4,6,8]
--    (==)

-- partial
-- testIntersection : Test (List Int)
-- testIntersection = MkTest
--     (Just "Intersection")
--     (Tree.toList $ Tree.intersection
--         (Tree.fromList [1,2,3,4,5,6,7,8,9])
--         (Tree.fromList [1,2,33,44,55,66,77,88,99]))
--     [1,2]
--     (==)

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
