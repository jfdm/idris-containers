module Data.Algebraic.Graph

%default total
%access public export

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

foldg : (init : type)
     -> (whenVertex  : a -> type)
     -> (whenOverlay : type -> type -> type)
     -> (whenConnect : type -> type -> type)
     -> (graph : Graph a)
     -> type
foldg init whenVertex whenOverlay whenConnect = go
  where
    go : Graph a -> type
    go Empty = init
    go (Vertex elem) = whenVertex elem
    go (Overlay x y) = whenOverlay (go x) (go y)
    go (Connect x y) = whenConnect (go x) (go y)


overlays : List (Graph a) -> Graph a
overlays = foldr overlay empty

vertices : List a -> Graph a
vertices = overlays . map vertex

connects : List (Graph a) -> Graph a
connects = foldr connect empty

edges : List (a,a) -> Graph a
edges = overlays . map (uncurry edge)

graph : List a -> List (a,a) -> Graph a
graph vs es = overlay (vertices vs) (edges es)

data HasVertex : (elem : type) -> Graph type -> Type where
  Here : HasVertex e (Vertex e)
  ThereOL : HasVertex e l
         -> HasVertex e (Overlay l r)
  ThereOR : HasVertex e r
         -> HasVertex e (Overlay l r)
  ThereCL : HasVertex e l
         -> HasVertex e (Connect l r)
  ThereCR : HasVertex e r
         -> HasVertex e (Connect l r)

graphIsEmpty : HasVertex e Empty -> Void
graphIsEmpty Here impossible
graphIsEmpty (ThereOL _) impossible
graphIsEmpty (ThereOR _) impossible
graphIsEmpty (ThereCL _) impossible
graphIsEmpty (ThereCR _) impossible

notSameVertex : (contra : (e = x) -> Void) -> HasVertex e (Vertex x) -> Void
notSameVertex contra Here = contra Refl

notOverlay : (contra : HasVertex e x -> Void)
         -> (f : HasVertex e y -> Void)
         -> HasVertex e (Overlay x y)
         -> Void
notOverlay contra f x with (x)
  notOverlay contra f x | (ThereOL y) = contra y
  notOverlay contra f x | (ThereOR y) = f y


notConnect : (contra : HasVertex e x -> Void)
          -> (f : HasVertex e y -> Void)
          -> HasVertex e (Connect x y)
          -> Void
notConnect contra f x with (x)
  notConnect contra f x | (ThereCL y) = contra y
  notConnect contra f x | (ThereCR y) = f y


hasVertex : DecEq type => (elem : type) -> (graph : Graph type) -> Dec (HasVertex elem graph)
hasVertex elem Empty = No graphIsEmpty
hasVertex elem (Vertex x) with (decEq elem x)
  hasVertex x (Vertex x) | (Yes Refl) = Yes Here
  hasVertex elem (Vertex x) | (No contra) = No (notSameVertex contra)

hasVertex elem (Overlay x y) with (hasVertex elem x)
  hasVertex elem (Overlay x y) | (Yes prf) = Yes (ThereOL prf)
  hasVertex elem (Overlay x y) | (No contra) with (hasVertex elem y)
    hasVertex elem (Overlay x y) | (No contra) | (Yes prf) = Yes (ThereOR prf)
    hasVertex elem (Overlay x y) | (No contra) | (No f) = No (notOverlay contra f)


hasVertex elem (Connect x y) with (hasVertex elem x)
  hasVertex elem (Connect x y) | (Yes prf) = Yes (ThereCL prf)
  hasVertex elem (Connect x y) | (No contra) with (hasVertex elem y)
    hasVertex elem (Connect x y) | (No contra) | (Yes prf) = Yes (ThereCR prf)
    hasVertex elem (Connect x y) | (No contra) | (No f) = No (notConnect contra f)
