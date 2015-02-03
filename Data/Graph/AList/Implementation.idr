||| A Graph implementation based on Adjacency Lists.
module Data.Graph.AList.Implementation

import public Data.AVL.Dict
import public Data.Graph.Common

%access public

-- ------------------------------------------------------------------- [ Types ]
||| A compact adjacency list representation of a graph.
|||
||| Note a BST based (AVL) Dictionary is used as the underlying data
||| structure, access to a node will be `O(log n)`. Constant time
||| access to elements in the graph is not guaranteed.
|||
||| @vTy The type of the value associated with the vertex.
||| @eTy The type of the label used on edges.
Graph : (vTy : Type) -> (eTy : Type) -> Type
Graph n e = Dict (LNode n) (AList e)

verticies : Graph v e -> List (LNode v)
verticies Empty = Nil
verticies (Node _ (k,as) l r) = verticies l ++ [k] ++ verticies r

edges : Graph v e -> List Edge
edges Empty = Nil
edges (Node _ ((i,v),(as)) l r) = foldEdge i as ++ edges l ++ edges r
  where
    foldEdge : Node -> AList e -> List (Node, Node)
    foldEdge v Nil         = Nil
    foldEdge v ((i,l)::es) = (v,i) :: foldEdge v es

private
selectNode : Node -> LNode v -> Ordering
selectNode x (y,_) = compare x y

addNode : Ord v => LNode v -> Graph v e -> Graph v e
addNode n g = insert n (Nil) g

addNodes : Ord v => List (LNode v) -> Graph v e -> Graph v e
addNodes ns g = foldl (flip $ addNode) g ns

addEdge : Ord v => LEdge e -> Graph v e -> Graph v e
addEdge (f,t,l) g = updateUsing (selectNode f) (\as => (t,l)::as) g

addEdges : Ord v => List (LEdge e) -> Graph v e -> Graph v e
addEdges es g = foldl (flip $ addEdge) g es

insertNode : Ord v => LNode v -> AList e -> Graph v e -> Graph v e
insertNode n es g = insert n es g

buildG : Ord v => List (LNode v) -> List (LEdge e) -> Graph v e
buildG Nil _    = Empty
buildG xs  Nil  = addNodes xs Empty
buildG ns  es   = addEdges es (addNodes ns Empty)

buildG' : Ord v => List (LNode v, AList e) -> Graph v e
buildG' gs = fromList gs

lookupNode : Ord v => Node -> Graph v e -> Maybe $ AList e
lookupNode n g = lookupUsing (selectNode n) g

getSuccsUsing : Ord v => (LNode v -> Ordering) -> Graph v e -> Maybe $ List Node
getSuccsUsing f g = case lookupUsing f g of
    Just as => Just $ map fst as
    Nothing => Nothing

getSuccsByID : Ord v => Node -> Graph v e -> Maybe $ List Node
getSuccsByID n g = getSuccsUsing (selectNode n) g

getSuccsByLabel : Ord v => v -> Graph v e -> Maybe $ List Node
getSuccsByLabel x g = getSuccsUsing (\(i,y) => compare x y) g

-- --------------------------------------------------------------------- [ EOF ]
