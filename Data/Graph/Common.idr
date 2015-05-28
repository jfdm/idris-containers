||| Common definitions and functions for graph implementations.
module Data.Graph.Common

-- ------------------------------------------------------------------- [ Nodes ]
||| Node Identifier
Node : Type
Node = Int

||| Labelled Nodes
LNode : Type -> Type
LNode a = (Node, a)

||| Unlabelled Nodes
UNode : Type
UNode = LNode ()

-- ------------------------------------------------------------------- [ Edges ]

||| Edge between two nodes.
Edge : Type
Edge = (Node, Node)

||| A labelled edge between two nodes.
LEdge : Type -> Type
LEdge b = (Node, Node, b)

||| An unlabelled edge between two nodes.
UEdge : Type
UEdge = LEdge ()

-- ------------------------------------------------------------------- [ Paths ]

||| Paths
Path : Type
Path = List Node

||| Labelled Paths
data LPath a = LP (LPath a)

instance Show a => Show (LPath a) where
  show (LP xs) = show xs

||| Adjacency list denoting adjacent nodes in the graph.
||| The list is a `(node, label)` pairing.
AList : Type -> Type
AList b = List (Node, b)


-- --------------------------------------------------------------------- [ EOF ]
