||| Testing IntMap using silly stupid tests
module Data.Test.Patricia

import Test.Generic
import Test.Random

import Data.Patricia.IntMap

%access export

----------------------------------------------------------------------------
-- Maps to test
----------------------------------------------------------------------------

initMap : Int32Map String
initMap = fromList [(1,"a"), (2,"b"), (3,"c"), (4, "d"), (4, "x")]

biggerMap : Int32Map String
biggerMap = insert 5 "e" initMap

lesserMap : Int32Map String
lesserMap = delete 10 $ delete 5 $ delete 2 biggerMap

----------------------------------------------------------------------------
-- Tests
----------------------------------------------------------------------------

partial
testBuildingSize : IO Bool
testBuildingSize = genericTest
    (Just "Sizes")
    [size initMap, size biggerMap, size lesserMap]
    [4, 5, 3]
    (==)

partial
testLookups : IO Bool
testLookups = genericTest
    (Just "Lookups")
    [ lookup 2 initMap
    , lookup 4 initMap
    , lookup 0 initMap
    , lookup 5 biggerMap
    , lookup 5 lesserMap
    , lookup 2 lesserMap
    , lookup 3 lesserMap
    ]
    [Just "b", Just "x", Nothing, Just "e", Nothing, Nothing, Just "c"]
    (==)

partial
testToListValues : IO Bool
testToListValues = genericTest
    (Just "Keys")
    [values initMap      , values biggerMap         , values lesserMap]
    [["a", "b", "c", "x"], ["a", "b", "c", "x", "e"], ["a", "c", "x"] ]
    (==)

----------------------------------------------------------------------------
-- Test runner
----------------------------------------------------------------------------

partial
runTest : IO ()
runTest = do
    putStrLn "Testing Patricia.IntMap"
    putStrLn infoLine
    NonReporting.runTests
      [ testBuildingSize
      , testLookups
      , testToListValues
      ]
