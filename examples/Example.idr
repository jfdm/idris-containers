module Example

import Data.Graph.AList
import Data.RoseTree
import Data.AVL.Set
import Data.Stack

towns : List String
towns = ["Munchen", "Augsburg", "Nurnberg","Stuttgart",
         "Kassel",
         "Erfurt",
         "Wurzburg",
         "Karlsruhe",
         "Frankfurt",
          "Mannheim"]

links : List (String, String, Int)
links = [("Frankfurt", "Mannheim", 85),
         ("Frankfurt","Wurzburg",217),
         ("Frankfurt","Kassel",173),
        ("Mannheim","Karlsruhe", 80),
        ("Karlsruhe","Ausburg", 250),
        ("Ausburg","Munchen", 84),
        ("Wurzburg","Erfurt", 186),
        ("Wurzburg","Nurnburg", 167),
        ("Nurnburg","Stuttgart", 183),
        ("Nurnburg","Munchen", 167),
        ("Kassel","Munchen", 502)]

g : Graph String Int
g = buildG towns links

 -- g1 : Graph String String
 -- g1 = buildG (zip [1..4] ["a", "b", "c", "d"] Refl) [("Munchen","Ausburg","a"),("Nurnburg","Ausburg","b"),("Munchen","Stuttgart","a")]



-- --------------------------------------------------------------------- [ DFS ]

namespace Main
  main : IO ()
  main = do
    putStrLn "A Graph"
    putStrLn $ show g

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
