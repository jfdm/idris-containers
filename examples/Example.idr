module Example

import Effects
import Effect.State
import Effect.StdIO

import Data.Graph.AList
import Data.RoseTree
import Data.AVL.Set
import Data.Stack

towns : List $ LNode String
towns = [(1, "Munchen"),
         (2, "Augsburg"),
         (3, "Nurnberg"),
         (4, "Stuttgart"),
         (5, "Kassel"),
         (6, "Erfurt"),
         (7, "Wurzburg"),
         (8, "Karlsruhe"),
         (9, "Frankfurt"),
         (10, "Mannheim")]

links : List $ LEdge Int
links = [(9, 10, 85), (9,7,217), (9,5,173),
        (10,8, 80),
        (8,2, 250),
        (2,1, 84),
        (7,6, 186),
        (7,3, 167),
        (3,4, 183),
        (3,1, 167),
        (5,1, 502)]

g : Graph String Int
g = buildG towns links

g1 : Graph String String
g1 = buildG (zip [1..4] ["a", "b", "c", "d"] Refl) [(1,2,"a"),(3,2,"b"),(1,4,"a")]



-- --------------------------------------------------------------------- [ DFS ]

namespace Main
  main : IO ()
  main = do
    putStrLn "A Graph"
    putStrLn $ show g
    putStrLn "Trace of a Depth First Traversal"
    traceDfsIO 9 g
    putStrLn "Trace of a Breadth First Traversal"
    traceBfsIO 9 g


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
