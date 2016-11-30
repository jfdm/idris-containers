-- --------------------------------------------------------------- [ Graph.idr ]
-- Module    : Graph.idr
-- Copyright : (c) 2015,2016 See CONTRIBUTORS.md
-- License   : see LICENSE
-- --------------------------------------------------------------------- [ EOH ]
||| Testing Stacks using silly stupid tests
module Data.AVL.Test.Graph

import Test.Generic
import Data.AVL.Graph

%access export
-- ------------------------------------------------------------ [ Construction ]

towns : List String
towns = ["Munchen",
         "Augsburg",
         "Nurnburg",
         "Stuttgart",
         "Kassel",
         "Erfurt",
         "Wurzburg",
         "Karlsruhe",
         "Frankfurt",
         "Mannheim"]

links : List (String, String, Maybe Int)
links = [("Frankfurt"  ,"Mannheim" , Just 85),
         ("Frankfurt"  ,"Wurzburg"  , Just 217),
         ("Frankfurt"  ,"Kassel"    , Just 173),
         ("Mannheim"   ,"Karlsruhe" , Just 80),
         ("Karlsruhe"  ,"Augsburg"  , Just 250),
         ("Augsburg"   ,"Munchen"   , Just 84),
         ("Wurzburg"   ,"Erfurt"    , Just 186),
         ("Wurzburg"   ,"Nurnburg"  , Just 167),
         ("Nurnburg"   ,"Stuttgart" , Just 183),
         ("Nurnburg"   ,"Munchen"   , Just 167),
         ("Kassel"     ,"Munchen"   , Just 502)]

g : Graph String Int
g = with List buildG towns links

-- ---------------------------------------------------------------- [ Updating ]
partial
testBuild : IO Bool
testBuild = genericTest
    (Just "Insert")
    [ hasValue "Frankfurt" g
    , hasValue "Kassel" g
    , hasValue "Dortmund" g
    , hasValue "Berlin" g]
    [True,True,False,False]
    (==)

partial
testSuccs : IO Bool
testSuccs = genericTest
    (Just "Succs")
    (getSuccs "Wurzburg" g)
    [2,5]
    (==)

partial
testEdges : IO Bool
testEdges = genericTest
    (Just "Edges")
    ([getEdgesByID 0 g, getEdges "Kassel" g])
    ([Nil, [(0, Just 502)]])
    (==)

partial
testLeafs : IO Bool
testLeafs = genericTest
  (Just "Get Leaf Nodes")
  (catMaybes $ map (\x => getValueByID x g) (leafNodes g))
  ["Erfurt", "Stuttgart", "Munchen"]
  (\x,y => sort x == sort y)

partial
testRoots : IO Bool
testRoots = genericTest
  (Just "Get Root Nodes")
  (getValuesByID (rootNodes g) g)
  ["Frankfurt"]
  (\x,y => sort x == sort y)

partial
testDiscon : IO Bool
testDiscon = genericTest
  (Just "Disconnected")
  (isDisconnected g)
  False
  (==)

partial
testDiscon2 : IO Bool
testDiscon2 = genericTest
  (Just "Disconnected")
  (isDisconnected (addNode "Aachen" g))
  True
  (==)


partial
runTest : IO ()
runTest = do
    putStrLn "Testing Graph"
    putStrLn infoLine
    NonReporting.runTests [
        testBuild
      , testSuccs
      , testEdges
      , testLeafs
      , testRoots
      , testDiscon
      , testDiscon2
    ]

-- --------------------------------------------------------------------- [ EOF ]
