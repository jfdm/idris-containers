||| A Graph implementation based on Adjacency Lists.
|||
||| The underlying implementation is that of an AVL-based Dictionary
||| that associates a `(id,value)` pair to an adjacency list
||| `(id,label)`.
module Data.AVL.Graph

import public Data.AVL.Dict

%access public

||| Node Identifier
NodeID : Type
NodeID = Nat

||| A labelled edge between two nodes using NodeID
Edge : Type -> Type
Edge b = (NodeID, NodeID, Maybe b)

||| A demi labeld Edge
DemiEdge : Type -> Type
DemiEdge b = (NodeID, Maybe b)

||| Adjacency 'list' denoting adjacent nodes in the graph.
||| The list is a dict between destination `NodeID` and label.
|||
||| Note:: Should probably change this to a dict with a list of edges,
||| but that is too much work at the momemt.
AList : Type -> Type
AList b = List (NodeID, Maybe b)

-- ------------------------------------------------------------------- [ Types ]

||| A compact adjacency list representation of a graph.
|||
||| Implementation details:
|||
||| The Graph is actually a record that contains:
|||
||| 1. A labelling `counter`.
||| 2. An association list to contain value to identifier pairings.
||| 3. A BST-based dictionary containing the adjacency Lists.
|||
||| A BST based (AVL) Dictionary is used as the underlying data
||| structure, access to a node's adjaceny list should be `O(log
||| n)`. Constant time access to elements in the graph is not
||| guaranteed.
|||
||| The dictionary is indexed using a *Node Identifier* (`Nat`), as
||| Idris does not have support for hashes, cryptographic or
||| otherwise. Future work will be to replace the simple labelling
||| mnemoic with a hash. As such we need a secondary map to keep
||| record of what values map to what `NodeID`. To simplify matters a
||| association list is used to reduce the need for values in the
||| graph to be orderable.
|||
||| The dictionary stores a node value, successor list pairing as the
||| value.
|||
||| @vTy The type of the value associated with the vertex.
||| @eTy The type of the label used on edges.
record Graph (vTy : Type) (eTy : Type) where
  constructor MkGraph
  counter : NodeID
  legend  : List (vTy, NodeID)
  graph   : Dict (NodeID) (vTy, AList eTy)

GraphRep : (vTy : Type) -> (eTy : Type) -> Type
GraphRep vTy eTy = Dict (NodeID) (vTy, AList eTy)

Legend : Type -> Type
Legend vTy = List (vTy, NodeID)


instance (Show v, Show e) => Show (Graph v e) where
  show (MkGraph _ _ Empty) = "[Empty Graph]"
  show (MkGraph _ _ g)     = show g

-- ---------------------------------------------------------- [ Legend Utility ]
private
delFromLegend : ((v,NodeID) -> Bool) -> Legend v -> Legend v
delFromLegend f Nil = Nil
delFromLegend f (x::xs) =
  if f x
    then xs
    else x::xs

private
insertLegend : Eq v => v -> NodeID -> Legend v -> Legend v
insertLegend val id l = (val, id) :: delFromLegend (\(x,_) => x == val) l

private
updateLegend : Eq v => v -> Legend v -> Legend v
updateLegend x l = map (\(y,id) => if x == y then (x,id) else (y,id)) l

-- ------------------------------------------------------------ [ Construction ]

mkEmptyGraph : Graph v e
mkEmptyGraph = MkGraph Z Nil Empty


||| Add an orphan node to the graph.
|||
||| To insert a connected node use `insert` instead.
addNode : Eq v => v -> Graph v e -> Graph v e
addNode val (MkGraph c l g) = MkGraph (S c) newL newG
  where
    newG : GraphRep v e
    newG = insert c (val,Nil) g

    newL : Legend v
    newL = insertLegend val c l

||| Add many orphan nodes to the graph.
addNodes : Eq v => List v -> Graph v e -> Graph v e
addNodes vs g = foldl (flip $ addNode) g vs

||| For a given value return the node id
getNodeID : Eq v => v -> Graph v e -> Maybe NodeID
getNodeID v g = List.lookup v (legend g)


||| Add a labelled edge to the Graph.
addEdge : Edge e -> Graph v e -> Graph v e
addEdge (x,y,l) g =
    case validEdge x y of
      True  => record {graph = doUpdate (x,y,l) (graph g)} g
      False => g
  where
    validEdge : NodeID -> NodeID -> Bool
    validEdge x y = isKey x (graph g) && isKey y (graph g)

    doUpdate : (NodeID, NodeID, Maybe e) -> GraphRep v e -> GraphRep v e
    doUpdate (x,y,l) gr = update x (\(val,as) => (val, (y,l)::as)) gr

||| Add multiple labelled edges to the Graph.
addEdges : List (Edge e) -> Graph v e -> Graph v e
addEdges es g = foldl (flip $ addEdge) g es

||| Add Value Edge
addValueEdge : Eq v => (v, v, Maybe e) -> Graph v e -> Graph v e
addValueEdge l g =
    case newEdge l of
      Just e' => addEdge e' g
      Nothing => g
  where
    conv : v -> v -> Maybe (NodeID, NodeID)
    conv x y = [(xID, yID) | xID <- getNodeID x g,
                             yID <- getNodeID y g]

    newEdge : (v, v, Maybe e) -> Maybe $ (Edge e)
    newEdge (x,y,l) =
      case conv x y of
        Just (xID, yID) => Just (xID,yID,l)
        otherwise       => Nothing

addValueEdges : Eq v => List (v,v, Maybe e) -> Graph v e -> Graph v e
addValueEdges vs g  = foldl (flip $ addValueEdge) g vs

||| Insert a node, complete with predefined adjacency list to the graph.
insertNode : Eq v => v -> AList e -> Graph v e -> Graph v e
insertNode val es (MkGraph c l g) = MkGraph (S c) newL (insert c (val,es) g)
  where
    newL : Legend v
    newL = insertLegend val c l

-- ------------------------------------------------------------------- [ Dumps ]

||| Return the a list of node identifiers used in the graph.
verticesID : Graph v e -> List NodeID
verticesID g = map (snd) (legend g)

||| Return the list of nodes in the graph.
vertices : Graph v e -> List v
vertices g = map (fst) (legend g)

||| Return the list of edges within the graph.
edges : Graph v e -> List (Edge e)
edges = (func . graph)
  where
    func : GraphRep v e -> List (Edge e)
    func Empty = Nil
    func (Node _ (id,(val,as)) l r) =
        foldl (\xs,(id',l) => (id,id',l)::xs) Nil as ++ func l ++ func r

-- ----------------------------------------------------------------- [ Lookups ]

||| Using Node ID, extract the node value and adjacency list from the graph.
lookupNodeByID : NodeID -> Graph v e -> Maybe $ (v, AList e)
lookupNodeByID n g = lookup n (graph g)

||| Using the node value, extract the node value and adjaceny list from the graph.
lookupNode : Eq v => v -> Graph v e -> Maybe (v, AList e)
lookupNode val g =
  case List.lookup val (legend g) of
    Just id => lookup id (graph g)
    Nothing => Nothing

-- ----------------------------------------------------------------- [ Queries ]

||| Does the graph contain a node with a specific value.
hasValue : Eq v => v -> Graph v e -> Bool
hasValue v g = isJust $ getNodeID v g

||| Get a nodes value
getValue : NodeID -> Graph v e -> Maybe v
getValue id g =
   case lookup id (graph g) of
      Just (val,_) => Just val
      Nothing      => Nothing

||| Get a nodes successors.
getSuccsByID : NodeID -> Graph v e -> List NodeID
getSuccsByID id g =
  case lookup id (graph g) of
    Just (_,as) => map fst as
    Nothing     => Nil

||| Get a nodes successor
getSuccs : Eq v => v -> Graph v e -> List NodeID
getSuccs val g =
  case getNodeID val g of
    Nothing => Nil
    Just id => getSuccsByID id g

||| Get the adjaceny list for an node
getEdgesByID : NodeID -> Graph v e -> List (DemiEdge e)
getEdgesByID id g =
  case lookup id (graph g) of
    Nothing     => Nil
    Just (_,as) => as

||| Get the adjaceny list for an node.
getEdges : Eq v => v -> Graph v e -> List (DemiEdge e)
getEdges val g =
  case getNodeID val g of
    Just id => getEdgesByID id g
    Nothing => Nil

||| Get the full edge description
getEdgesVerboseByID : NodeID -> Graph v e -> List (Edge e)
getEdgesVerboseByID id g =
  case lookup id (graph g) of
    Nothing     => Nil
    Just (_,as) => map (\(destID,label) => (id,destID,label)) as

||| Get the full edge description
getEdgesVerbose : Eq v => v -> Graph v e -> List (Edge e)
getEdgesVerbose val g =
  case getNodeID val g of
    Just id => getEdgesVerboseByID id g
    Nothing => Nil

-- ----------------------------------------------------------------- [ Updates ]
updateNodeValueByID : Eq v => NodeID -> v -> Graph v e -> Graph v e
updateNodeValueByID id val g = record {graph = newG, legend = newL} g
  where
    newG : GraphRep v e
    newG = update id (\(val',as) => (val,as)) (graph g)

    newL : Legend v
    newL = updateLegend val (legend g)

-- ------------------------------------------------------------- [ Build Graph ]

||| Construct a graph using a list of nodes and a list of edges.
buildG : Eq v => List v -> List (v,v, Maybe e) -> Graph v e
buildG Nil _  = mkEmptyGraph
buildG ns  es = record {counter = (S maxID)} g
  where
    g : Graph v e
    g = addNodes ns mkEmptyGraph

    g' : Graph v e
    g' = addValueEdges es g

    maxID : NodeID
    maxID = foldl (\x, (_,id) => max x id) Z (legend g')

-- --------------------------------------------------------------------- [ EOF ]
