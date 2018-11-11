module Data.Algebraic.Graph

%default total
%access public export

data Graph : Type -> Type where
  Empty  : Graph type
  Vertex : (value : type) -> Graph type
  Overlay : (left : Graph type) -> (right : Graph type) -> Graph type
  Connect : (left : Graph type) -> (right : Graph type) -> Graph type

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

namespace HasVertex
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

  hasVertex : DecEq type
           => (elem : type)
           -> (graph : Graph type)
           -> Dec (HasVertex elem graph)
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

namespace HasEdge
  EdgeProof : (type : Type) -> Type
  EdgeProof type = (a,b : type) -> Graph type -> Type

  ||| Proof that a Connect with a heirarchical l and r graph has a connection.
  data HasEdge : EdgeProof type where
    IsConnectEdge : HasVertex a l
                 -> HasVertex b r
                 -> HasEdge a b (Connect l r)
    IsOverlayL : HasEdge a b l -> HasEdge a b (Overlay l r)
    IsOverlayR : HasEdge a b r -> HasEdge a b (Overlay l r)

  isEmpty : HasEdge a b Empty -> Void
  isEmpty (IsConnectEdge _ _) impossible
  isEmpty (IsOverlayL _) impossible
  isEmpty (IsOverlayR _) impossible

  isVertex : HasEdge a b (Vertex value) -> Void
  isVertex (IsConnectEdge _ _) impossible
  isVertex (IsOverlayL _) impossible
  isVertex (IsOverlayR _) impossible

  notLeftNotRight : (contra : HasEdge a b left -> Void)
                 -> (f : HasEdge a b right -> Void)
                 -> HasEdge a b (Overlay left right)
                 -> Void
  notLeftNotRight contra f (IsOverlayL x) = contra x
  notLeftNotRight contra f (IsOverlayR x) = f x

  notLeft : (contra : HasVertex a left -> Void)
         -> HasEdge a b (Connect left right)
         -> Void
  notLeft contra (IsConnectEdge x y) = contra x

  notRight : (contra : HasVertex b right -> Void)
          -> HasEdge a b (Connect left right)
          -> Void
  notRight contra (IsConnectEdge x y) = contra y

  hasEdge : DecEq type
                       => (a,b : type)
                       -> (graph : Graph type)
                       -> Dec (HasEdge a b graph)
  hasEdge a b Empty = No isEmpty
  hasEdge a b (Vertex value) = No isVertex
  hasEdge a b (Overlay left right) with (hasEdge a b left)
    hasEdge a b (Overlay left right) | (Yes prf) = Yes (IsOverlayL prf)
    hasEdge a b (Overlay left right) | (No contra) with (hasEdge a b right)
      hasEdge a b (Overlay left right) | (No contra) | (Yes prf) = Yes (IsOverlayR prf)
      hasEdge a b (Overlay left right) | (No contra) | (No f) = No (notLeftNotRight contra f)


  hasEdge a b (Connect left right) with (hasVertex a left)
    hasEdge a b (Connect left right) | (Yes prf) with (hasVertex b right)
      hasEdge a b (Connect left right) | (Yes prf) | (Yes x) = Yes (IsConnectEdge prf x)
      hasEdge a b (Connect left right) | (Yes prf) | (No contra) = No (notRight contra)

    hasEdge a b (Connect left right) | (No contra) = No (notLeft contra)
