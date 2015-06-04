module Example

import Data.AVL.Dependent.Graph


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

 -- g1 : Graph String String
 -- g1 = buildG (zip [1..4] ["a", "b", "c", "d"] Refl) [("Munchen","Ausburg","a"),("Nurnburg","Ausburg","b"),("Munchen","Stuttgart","a")]


data HasNode : String -> Graph String Int -> Type where
  Has : HasNode a g

hasNode : (a : String) -> (g : Graph String Int) -> Dec (HasNode a g)
hasNode val g = case hasValue val g of
  True  => Yes (Has)
  False => No (believe_me)

gs : List Bool
gs = map (\x => doCheck x g) towns
  where
    doCheck : String -> Graph String Int -> Bool
    doCheck x g with (hasNode x g)
      | Yes prf = True
      | No  con = False
-- --------------------------------------------------------------------- [ DFS ]

namespace Main
  main : IO ()
  main = do
    putStrLn "A Graph"
    putStrLn $ show g

    printLn gs

    printLn (updateNodeValueUsing "Mannheim" (\x => "as") g)

    -- putStrLn "Trace of a Depth First Traversal"
    -- traceDfsIO 9 g
    -- putStrLn "Trace of a Breadth First Traversal"
    -- traceBfsIO 9 g


{-
9
5
7
10
1
3
6
8
4
2
-}
