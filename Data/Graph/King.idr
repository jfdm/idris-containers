||| A version of the graph algorithms described in:
|||
|||   /Structuring Depth-First Search Algorithms in Haskell/,
|||   by David King and John Launchbury.
module Data.Graph.King

import public Data.AVL.Dict
import public Data.Graph.Common

%access public

-- ------------------------------------------------------------------- [ Types ]
||| A compact adjacency list representation of a graph.
|||
||| Note a BST based (AVL) Dictionary is used as the underlying data
||| structure, access to a node will be `O(log n)`. Constant time
||| access to elements in the graph is not guaranteed.
Graph : Type -> Type -> Type
Graph n e = Dict (Node) (n, AList e)

verticies : Graph v e -> List (LNode v)
verticies Empty = Nil
verticies (Node _ (k,(v,as)) l r) = verticies l ++ [(k,v)] ++ verticies r

edges : Graph v e -> List Edge
edges Empty = Nil
edges (Node _ (k,(v,as)) l r) = foldEdge k as ++ edges l ++ edges r
  where
    foldEdge : Node -> AList e -> List (Node, Node)
    foldEdge v Nil         = Nil
    foldEdge v ((n,l)::es) = (v,n) :: foldEdge v es


addNode : Ord v => LNode v -> Graph v e -> Graph v e
addNode (n,val) g = insert n (val,Nil) g

addNodes : Ord v => List (LNode v) -> Graph v e -> Graph v e
addNodes ns g = foldl (\g', (n,v) => insert n (v,Nil) g') g ns

addEdge : LEdge e -> Graph v e -> Graph v e
addEdge (f,t,l) g = update f (\(v,as) => (v,(t,l)::as)) g

addEdges : List (LEdge e) -> Graph v e -> Graph v e
addEdges es g = foldl (flip $ addEdge) g es

insertNode : Ord v => LNode v -> AList e -> Graph v e -> Graph v e
insertNode (n,val) es g = insert n (val,es) g

buildG : Ord v => List (LNode v) -> List (LEdge e) -> Graph v e
buildG Nil _    = Empty
buildG xs  Nil  = addNodes xs Empty
buildG ns  es   = addEdges es (addNodes ns Empty)

buildG' : List (Node, n, AList e) -> Graph n e
buildG' gs = fromList gs

getSuccs : Node -> Graph v e -> Maybe $ List Node
getSuccs n g = case lookup n g of
    Just (val,as) => Just $ map fst as
    Nothing       => Nothing

-- --------------------------------------------------------------------- [ EOF ]
