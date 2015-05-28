||| A Graph implementation based on Adjacency Lists.
|||
||| The underlying implementation is that of an AVL-based Dictionary
||| that associates a `(id,value)` pair to an adjacency list
||| `(id,label)`.
module Data.Graph.AList

import public Data.AVL.Dict
import public Data.Graph.Common

%access public

-- ------------------------------------------------------------------- [ Types ]
record Graph (vTy : Type) (eTy : Type) where
  constructor MkGraph
  counter : Int
  graph : Dict (Node) (vTy, AList eTy)

||| A compact adjacency list representation of a graph.
|||
||| Note a BST based (AVL) Dictionary is used as the underlying data
||| structure, access to a node will be `O(log n)`. Constant time
||| access to elements in the graph is not guaranteed.
|||
||| The dictionary is indexed using a *Node Identifier* (`Int`). The
||| dictionary stores a node value, successor list pairing as the value.
|||
||| We also store an Nat that is used for auto assignment of node id's
||| during insertion.
|||
||| @vTy The type of the value associated with the vertex.
||| @eTy The type of the label used on edges.
GraphRep : (vTy : Type) -> (eTy : Type) -> Type
GraphRep vTy eTy = Dict (Node) (vTy, AList eTy)

instance (Show v, Show e) => Show (Graph v e) where
  show (MkGraph _ Empty) = "[Empty Graph]"
  show (MkGraph _ g)     = show g

mkEmptyGraph : Graph v e
mkEmptyGraph = MkGraph 0 Empty

||| Return the a list of node identifiers used in the graph.
vertices : Graph v e -> List Node
vertices g = (func . graph) g
  where
    func : GraphRep v e -> List Node
    func Empty = Nil
    func (Node _ (k,as) l r) = func l ++ [k] ++ func r

||| Return the list of edges (unlabelled) with in the graph.
edges : Graph v e -> List Edge
edges = (func . graph)
  where
    func : GraphRep v e -> List Edge
    func Empty = Nil
    func (Node _ (id,(val,as)) l r) =
        foldl (\xs, (id',_) => (id,id')::xs) Nil as ++ func l ++ func r

||| Return the list of edges within the graph, complete with labels.
edgesL : Graph v e -> List (LEdge e)
edgesL = (func . graph)
  where
    func : GraphRep v e -> List (LEdge e)
    func Empty = Nil
    func (Node _ (id,(val,as)) l r) =
        foldl (\xs,(id',l) => (id,id',l)::xs) Nil as ++ func l ++ func r

||| Add an orphan node to the graph.
|||
||| To insert a connected node use `insert` instead.
addNode : v -> Graph v e -> Graph v e
addNode val (MkGraph c g) = MkGraph (c + 1) $ insert c (val,Nil) g

||| Add many orphan nodes to the graph.
addNodes : List v -> Graph v e -> Graph v e
addNodes vs g = foldl (flip $ addNode) g vs

||| Add a labelled edge to the Graph.
addEdge : LEdge e -> Graph v e -> Graph v e
addEdge l (MkGraph c g) = MkGraph c (func l g)
  where
    func : LEdge e -> GraphRep v e -> GraphRep v e
    func (f,t,l) g = update f (\(val,as) => (val,(t,l)::as)) g

||| Add multiple labelled edges to the Graph.
addEdges : List (LEdge e) -> Graph v e -> Graph v e
addEdges es g = foldl (flip $ addEdge) g es

||| Insert a node, complete with predefined adjacency list to the graph.
insertNode : v -> AList e -> Graph v e -> Graph v e
insertNode val es (MkGraph c g) = MkGraph (c + 1) (insert c (val,es) g)

||| Extract the node value and adjacency list from the graph.
lookupNode : Node -> Graph v e -> Maybe $ (v, AList e)
lookupNode n g = lookup n (graph g)


||| Does the graph contain a node with a specific value.
hasValue : Eq v => v -> Graph v e -> Bool
hasValue val g = hasValueUsing (\((x,_)) => x == val) (graph g)

getID : Eq v => v -> Graph v e -> Maybe Node
getID v g = getKeyUsing (\(x,_) => x == v) (graph g)

||| Get a nodes value
getValue : Node -> Graph v e -> Maybe v
getValue id g = case lookup id (graph g) of
    Just (val,_) => Just val
    Nothing      => Nothing

||| Get a nodes successors.
getSuccs : Node -> Graph v e -> Maybe $ List Node
getSuccs id g = case lookup id (graph g) of
    Just (_,as) => Just $ map fst as
    Nothing       => Nothing

getEdge : Node -> Graph v e -> Maybe $ List (Node, e)
getEdge id g = case lookup id (graph g) of
    Nothing     => Nothing
    Just (_,as) => Just as


findMaxID : Graph v e -> Node
findMaxID g = dofindMaxID 0 (toList (graph g))
  where
    dofindMaxID : Node -> List (Node,(v,AList e)) -> Node
    dofindMaxID max Nil = max
    dofindMaxID max ((curr,_)::rest) = case compare max curr of
      LT => dofindMaxID curr rest
      GT => dofindMaxID max rest
      EQ => dofindMaxID max rest

||| Construct a graph using a list of nodes and a list of edges.
buildG : Eq v => List v -> List (v,v,e) -> Graph v e
buildG Nil _    = mkEmptyGraph
buildG ns  es   = MkGraph ((findMaxID g) + 1) $ graph (addEdges es' g)
  where

    g : Graph v e
    g = addNodes ns mkEmptyGraph

    conv : (v,v,e) -> Maybe (LEdge e)
    conv (x,y,e) =
      case getID x g of
        Nothing => Nothing
        Just x' => case getID y g of
          Nothing => Nothing
          Just y' => Just (x',y',e)

    es' : List (LEdge e)
    es' = catMaybes $ map conv es
-- --------------------------------------------------------------------- [ EOF ]
