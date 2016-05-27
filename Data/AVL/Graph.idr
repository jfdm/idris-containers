-- --------------------------------------------------------------- [ Graph.idr ]
-- Module    : Graph.idr
-- Copyright : (c) 2015,2016 See CONTRIBUTORS.md
-- License   : see LICENSE
-- --------------------------------------------------------------------- [ EOH ]
||| A Graph implementation based on Adjacency Lists.
|||
||| The underlying implementation is that of an AVL-based Dictionary
||| that associates a `(id,value)` pair to an adjacency list
||| `(id,label)`.
module Data.AVL.Graph

import Data.AVL.Tree
import Data.AVL.Set

import public Data.AVL.Dict

%access export

||| Node Identifier
public export
NodeID : Type
NodeID = Nat

||| A labelled edge between two nodes using NodeID
public export
Edge : Type -> Type
Edge b = (NodeID, NodeID, Maybe b)

||| A demi labeld Edge
public export
DemiEdge : Type -> Type
DemiEdge b = (NodeID, Maybe b)

||| Adjacency 'list' denoting adjacent nodes in the graph.
||| The list is a dict between destination `NodeID` and label.
|||
||| Note:: Should probably c0hange this to a dict with a list of edges,
||| but that is too much work at the momemt.
public export
AList : Type -> Type
AList b = List (NodeID, Maybe b)

-- ------------------------------------------------------------------- [ Types ]
public export
GraphRep : (vTy : Type) -> (eTy : Type) -> Type
GraphRep vTy eTy = Dict NodeID (vTy, AList eTy)

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
public export
record Graph (vTy : Type) (eTy : Type) where
  constructor MkGraph
  counter : NodeID
  legend  : List (vTy, NodeID)
  graph   : GraphRep vTy eTy

public export
Legend : Type -> Type
Legend vTy = List (vTy, NodeID)


implementation (Show v, Show e) => Show (Graph v e) where
  show (MkGraph _ _ g) = show g

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
updateLegend : Eq v => v -> v -> Legend v -> Legend v
updateLegend old new l = map (\(x,id) => if x == old then (new,id) else (x,id)) l

-- ------------------------------------------------------------ [ Construction ]

mkEmptyGraph : Graph v e
mkEmptyGraph = MkGraph Z Nil empty


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

getNodeIDUsing : (v -> Bool) -> Graph v e -> Maybe NodeID
getNodeIDUsing f g = doLook f (legend g)
  where
    doLook : (v -> Bool) -> List (v,NodeID) -> Maybe NodeID
    doLook _ Nil         = Nothing
    doLook f ((x,id)::xs) = if f x then Just id else doLook f xs


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
    validEdge x' y' = hasKey x' (graph g) && hasKey y' (graph g)

    doUpdate : (NodeID, NodeID, Maybe e) -> GraphRep v e -> GraphRep v e
    doUpdate (x'',y'',l') gr = update x'' (\(val,as) => (val, (y'',l')::as)) gr

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
    conv x y =
      case getNodeID x g of
        Nothing  => Nothing
        Just xID =>
          case getNodeID y g of
            Nothing  => Nothing
            Just yID => Just (xID,yID)

    newEdge : (v, v, Maybe e) -> Maybe $ (Edge e)
    newEdge (x',y',l') =
      case conv x' y' of
        Just (xID', yID') => Just (xID',yID',l')
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
edges g = func $ toList $ graph g
  where
    func' : NodeID -> (v, AList e) -> List (Edge e)
    func' id (_,es) = map (\(y,l) => (id,y,l)) es

    func : List (NodeID, (v,AList e)) -> List (Edge e)
    func xs = foldl (\res,(x,y) => func' x y ++ res) Nil xs

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
getValueByID : NodeID -> Graph v e -> Maybe v
getValueByID id g =
   case lookup id (graph g) of
      Just (val,_) => Just val
      Nothing      => Nothing

||| Get Node Value
getValueUsing : (v -> Bool) -> Graph v e -> Maybe v
getValueUsing f g = doLook f (legend g)
  where
    doLook : (v -> Bool) -> List (v,NodeID) -> Maybe v
    doLook _ Nil         = Nothing
    doLook f ((x,_)::xs) = if f x then Just x else doLook f xs

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
private
updateLegendByID : NodeID -> (v -> v) -> Legend v -> Legend v
updateLegendByID x f l = map (\(oval,y) => if x == y then (f oval,y) else (oval,y)) l

updateNodeValueByIDUsing : Eq v => NodeID -> (v -> v) -> Graph v e -> Graph v e
updateNodeValueByIDUsing id f g = record {graph = newG id f, legend = newL id f} g
  where
    newG : Eq v => NodeID -> (v -> v) -> GraphRep v e
    newG i f = update i (\(o,as) => (f o, as)) (graph g)

    newL : NodeID -> (v -> v) -> Legend v
    newL i f = updateLegendByID i f (legend g)

updateNodeValueUsing : Eq v => v -> (v -> v) -> Graph v e -> Graph v e
updateNodeValueUsing oldval f g =
  case getNodeID oldval g of
    Nothing => g
    Just id => updateNodeValueByIDUsing id f g

replaceNodeValueByID : Eq v => NodeID -> v -> Graph v e -> Graph v e
replaceNodeValueByID id val g = updateNodeValueByIDUsing id (\x => val) g

replaceNodeValue : Eq v => v -> v -> Graph v e -> Graph v e
replaceNodeValue val newVal g =
  case getNodeID val g of
    Just id => replaceNodeValueByID id newVal g
    Nothing => g

-- -------------------------------------------------------------------- [ Misc ]

getValuesByID : List NodeID -> Graph v e -> List v
getValuesByID is g = catMaybes $ map (\x => getValueByID x g) is

-- foldr (\(v,id),res => if elem id is then v::res else res) List.Nil (legend g)

leafNodes : Graph v e -> List NodeID
leafNodes g = filter (\x => isNil (getSuccsByID x g)) (verticesID g)

rootNodes : Graph v e -> List NodeID
rootNodes g = Set.toList $ Set.difference parents succs
  where
    parents : Set NodeID
    parents = Set.fromList $ filter (\x => isCons (getSuccsByID x g)) (verticesID g)

    nodes : Set NodeID
    nodes = Set.fromList (verticesID g)

    succs : Set NodeID
    succs = Set.fromList $ concatMap (\x => getSuccsByID x g) (verticesID g)


disconnectedNodes : Graph v e -> List NodeID
disconnectedNodes g = Set.toList $ Set.difference (Set.fromList nodes) cNodes
  where
    nodes : List NodeID
    nodes = (verticesID g)

    yNodes : List NodeID
    yNodes = concatMap (\x => getSuccsByID x g) nodes

    xNodes : List NodeID
    xNodes = filter (\x => isCons (getSuccsByID x g)) nodes

    cNodes : Set NodeID
    cNodes = Set.fromList $ xNodes ++ yNodes

isDisconnected : Graph v e -> Bool
isDisconnected g = isCons $ (disconnectedNodes g)

-- ------------------------------------------------------------- [ Build Graph ]

||| Construct a graph using a list of nodes and a list of edges.
buildG : Eq v => List v -> List (v,v, Maybe e) -> Graph v e
buildG Nil _   = mkEmptyGraph
buildG ns  Nil = addNodes ns mkEmptyGraph
buildG ns  es  = addValueEdges es $ addNodes ns mkEmptyGraph
  where
    g : Graph v e
    g = addNodes ns mkEmptyGraph

    g' : Graph v e
    g' = addValueEdges es g

-- --------------------------------------------------------------------- [ EOF ]
