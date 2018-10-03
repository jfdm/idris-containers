module Data.Algebraic.Graph

%default total
%access export

data Graph : Type -> Type where
  Empty  : Graph type
  Vertex : (elem : type) -> Graph type
  Overlay : Graph type -> Graph type -> Graph type
  Connect : Graph type -> Graph type -> Graph type

Show type => Show (Graph type) where
  show Empty = "Empty"
  show (Vertex elem) = unwords ["Vertex", show elem]
  show (Overlay x y) = unwords ["Overlay", show x, show y]
  show (Connect x y) = unwords ["Connect", show x, show y]

Functor Graph where
  map func Empty = Empty
  map func (Vertex elem) = Vertex $ func elem
  map func (Overlay x y) = Overlay (map func x) (map func y)
  map func (Connect x y) = Connect (map func x) (map func y)

Foldable Graph where
  foldr func init Empty = init
  foldr func init (Vertex x) = func x init
  foldr func init (Overlay x y) = foldr func (foldr func init y) x
  foldr func init (Connect x y) = foldr func (foldr func init y) x

Traversable Graph where
  traverse func Empty = pure Empty
  traverse func (Vertex elem) = [| Vertex (func elem)|]
  traverse func (Overlay x y) = [| Overlay (traverse func x) (traverse func y) |]
  traverse func (Connect x y) = [| Connect (traverse func x) (traverse func y) |]

Num type => Num (Graph type) where
  fromInteger x = Vertex (fromInteger x)
  (+) = Overlay
  (*) = Connect

-- Do we need abs, negate, and signum?

empty : Graph a
empty = Empty

vertex : a -> Graph a
vertex a = Vertex a

connect : Graph a -> Graph a -> Graph a
connect = Connect

edge : a -> a -> Graph a
edge x y = connect (vertex x) (vertex y)

combine : Graph a -> Graph a -> Graph a
combine = Overlay

overlay : Graph a -> Graph a -> Graph a
overlay = combine
