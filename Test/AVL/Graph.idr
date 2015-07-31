||| Testing Stacks using silly stupid tests
module Test.AVL.Graph

import Test.Harness
import Data.AVL.Graph

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
testBuild : Test (List Bool)
testBuild = MkTest
    (Just "Insert")
    [ hasValue "Frankfurt" g
    , hasValue "Kassel" g
    , hasValue "Dortmund" g
    , hasValue "Berlin" g]
    [True,True,False,False]
    (==)

partial
testSuccs : Test (List Nat)
testSuccs = MkTest
    (Just "Succs")
    (getSuccs "Wurzburg" g)
    [2,5]
    (==)

partial
testEdges : Test (List $ List (DemiEdge Int))
testEdges = MkTest
    (Just "Edges")
    ([getEdgesByID 0 g, getEdges "Kassel" g])
    ([Nil, [(0, Just 502)]])
    (==)

partial
testLeafs : Test $ List String
testLeafs = MkTest
  (Just "Get Leaf Nodes")
  (catMaybes $ map (\x => getValueByID x g) (leafNodes g))
  ["Erfurt", "Stuttgart", "Munchen"]
  (\x,y => sort x == sort y)

partial
testRoots : Test $ List String
testRoots = MkTest
  (Just "Get Root Nodes")
  (catMaybes $ map (\x => getValueByID x g) (rootNodes g))
  ["Frankfurt"]
  (\x,y => sort x == sort y)

partial
testDiscon : Test Bool
testDiscon = MkTest
  (Just "Disconnected")
  (isDisconnected g)
  False
  (==)

partial
testDiscon2 : Test Bool
testDiscon2 = MkTest
  (Just "Disconnected")
  (isDisconnected (addNode "Aachen" g))
  True
  (==)


partial
runTest : IO ()
runTest = do
    putStrLn "Testing Graph"
    putStrLn infoLine
    runTests [
        testRunner testBuild
      , testRunner testSuccs
      , testRunner testEdges
      , testRunner testLeafs
      , testRunner testRoots
      , testRunner testDiscon
      , testRunner testDiscon2
    ]

-- --------------------------------------------------------------------- [ EOF ]
