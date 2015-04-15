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
||| The dictionary is indexed using a *Node Identifier* (`Int`). The
||| dictionary stores a node value, successor list pairing as the value.
|||
||| @vTy The type of the value associated with the vertex.
||| @eTy The type of the label used on edges.
Graph : (vTy : Type) -> (eTy : Type) -> Type
Graph n e = Dict (Node) (n, AList e)

||| Return the a list of node identifiers used in the graph.
verticies : Graph v e -> List Node
verticies Empty = Nil
verticies (Node _ (k,as) l r) = verticies l ++ [k] ++ verticies r

||| Return the list of edges (unlabelled) with in the graph.
edges : Graph v e -> List Edge
edges Empty = Nil
edges (Node _ (id,(val,as)) l r) =
    foldl (\xs, (id',_) => (id,id')::xs) Nil as ++ edges l ++ edges r

||| Return the list of edges within the graph, complete with labels.
edgesL : Graph v e -> List (LEdge e)
edgesL Empty = Nil
edgesL (Node _ (id,(val,as)) l r) =
    foldl (\xs,(id',l) => (id,id',l)::xs) Nil as ++ edgesL l ++ edgesL r

||| Add an orphan node to the graph.
|||
||| To insert a connected node use `insert` instead.
partial
addNode : LNode v -> Graph v e -> Graph v e
addNode (id,val) g = insert id (val,Nil) g

||| Add many orphan nodes to the graph.
|||
||| To insert a connected node use `insert` instead.
partial
addNodes : List (LNode v) -> Graph v e -> Graph v e
addNodes ns g = foldl (flip $ addNode) g ns

||| Add a labelled edge to the Graph.
partial
addEdge : LEdge e -> Graph v e -> Graph v e
addEdge (f,t,l) g = update f (\(val,as) => (val,(t,l)::as)) g

||| Add multiple labelled edges to the Graph.
partial
addEdges : List (LEdge e) -> Graph v e -> Graph v e
addEdges es g = foldl (flip $ addEdge) g es

||| Insert a node, complete with predefined adjacency list to the graph.
partial
insertNode : LNode v -> AList e -> Graph v e -> Graph v e
insertNode (id,val) es g = insert id (val,es) g

||| Construct a graph using a list of nodes and a list of edges.
partial
buildG : List (LNode v) -> List (LEdge e) -> Graph v e
buildG Nil _    = Empty
buildG xs  Nil  = addNodes xs Empty
buildG ns  es   = addEdges es (addNodes ns Empty)

||| Alternate build using a list of nodes and the node's adjacency list.
partial
buildG' : List (LNode v, AList e) -> Graph v e
buildG' gs = foldl (\g,(n,as) => insertNode n as g) Empty gs

||| Extract the node value and adjacency list from the graph.
lookupNode : Node -> Graph v e -> Maybe $ (v, AList e)
lookupNode n g = lookup n g

||| Get a nodes value
getValue : Node -> Graph v e -> Maybe v
getValue id g = case lookup id g of
    Just (val,_) => Just val
    Nothing      => Nothing

||| Get a nodes successors.
getSuccs : Node -> Graph v e -> Maybe $ List Node
getSuccs id g = case lookup id g of
    Just (_,as) => Just $ map fst as
    Nothing       => Nothing

-- --------------------------------------------------------------------- [ EOF ]
