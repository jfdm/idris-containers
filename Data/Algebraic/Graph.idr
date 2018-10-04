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

namespace HasEdge
  EdgeProof : (type : Type) -> Type
  EdgeProof type = (a,b : type) -> Graph type -> Type

  namespace Direct
    ||| Proof that there is an explicit connection between two vertices.
    data HasDirectEdge : EdgeProof type where
      IsDirectEdge : (a = x) -> (b = y) -> HasDirectEdge a b (Connect (Vertex x) (Vertex y))
      IsLeft : HasDirectEdge a b l
            -> HasDirectEdge a b (Overlay l r)
      IsRight : HasDirectEdge a b r
            -> HasDirectEdge a b (Overlay l r)

    hasDirectEdgeIsEmpty : HasDirectEdge a b Empty -> Void
    hasDirectEdgeIsEmpty IsDirectEdge impossible
    hasDirectEdgeIsEmpty (IsLeft _) impossible
    hasDirectEdgeIsEmpty (IsRight _) impossible

    hasDirectEdgeIsVertex : HasDirectEdge a b (Vertex value) -> Void
    hasDirectEdgeIsVertex IsDirectEdge impossible
    hasDirectEdgeIsVertex (IsLeft _) impossible
    hasDirectEdgeIsVertex (IsRight _) impossible

    notInLeftNotInRight : (contra : HasDirectEdge a b x -> Void) -> (f : HasDirectEdge a b y -> Void) -> HasDirectEdge a b (Overlay x y) -> Void
    notInLeftNotInRight contra f (IsLeft x) = contra x
    notInLeftNotInRight contra f (IsRight x) = f x


    notRightRight : (contra : (b = z) -> Void) -> HasDirectEdge value b (Connect (Vertex value) (Vertex z)) -> Void
    notRightRight contra (IsDirectEdge prf x) = contra x

    leftIsEmpty : HasDirectEdge value b (Connect (Vertex value) Empty) -> Void
    leftIsEmpty (IsDirectEdge _ _) impossible
    leftIsEmpty (IsLeft _) impossible
    leftIsEmpty (IsRight _) impossible

    leftIsOverlay : HasDirectEdge value b (Connect (Vertex value) (Overlay left right)) -> Void
    leftIsOverlay (IsDirectEdge _ _) impossible
    leftIsOverlay (IsLeft _) impossible
    leftIsOverlay (IsRight _) impossible

    leftIsConnect : HasDirectEdge value b (Connect (Vertex value) (Connect left right)) -> Void
    leftIsConnect (IsDirectEdge _ _) impossible
    leftIsConnect (IsLeft _) impossible
    leftIsConnect (IsRight _) impossible

    notRightLeft : (contra : (a = value) -> Void) -> HasDirectEdge a b (Connect (Vertex value) y) -> Void
    notRightLeft contra (IsDirectEdge prf x) = contra prf

    rightIsEmpty : HasDirectEdge a b (Connect Empty y) -> Void
    rightIsEmpty (IsDirectEdge _ _) impossible
    rightIsEmpty (IsLeft _) impossible
    rightIsEmpty (IsRight _) impossible

    rightIsOverlay : HasDirectEdge a b (Connect (Overlay left right) y) -> Void
    rightIsOverlay (IsDirectEdge _ _) impossible
    rightIsOverlay (IsLeft _) impossible
    rightIsOverlay (IsRight _) impossible

    rightIsConnect : HasDirectEdge a b (Connect (Connect left right) y) -> Void
    rightIsConnect (IsDirectEdge _ _) impossible
    rightIsConnect (IsLeft _) impossible
    rightIsConnect (IsRight _) impossible

    hasDirectEdge : DecEq type => (a,b : type) -> (graph : Graph type) -> Dec (HasDirectEdge a b graph)
    hasDirectEdge a b Empty = No hasDirectEdgeIsEmpty
    hasDirectEdge a b (Vertex elem) = No hasDirectEdgeIsVertex
    hasDirectEdge a b (Overlay x y) with (hasDirectEdge a b x)
      hasDirectEdge a b (Overlay x y) | (Yes prf) = Yes (IsLeft prf)
      hasDirectEdge a b (Overlay x y) | (No contra) with (hasDirectEdge a b y)
        hasDirectEdge a b (Overlay x y) | (No contra) | (Yes prf) = Yes (IsRight prf)
        hasDirectEdge a b (Overlay x y) | (No contra) | (No f) = No (notInLeftNotInRight contra f)

    hasDirectEdge a b (Connect x y) with (x)
      hasDirectEdge a b (Connect x y) | (Vertex value) with (decEq a value)
        hasDirectEdge value b (Connect x y) | (Vertex value) | (Yes Refl) with (y)
          hasDirectEdge value b (Connect x y) | (Vertex value) | (Yes Refl) | (Vertex z) with (decEq b z)
            hasDirectEdge value z (Connect x y) | (Vertex value) | (Yes Refl) | (Vertex z) | (Yes Refl) = Yes $ IsDirectEdge Refl Refl
            hasDirectEdge value b (Connect x y) | (Vertex value) | (Yes Refl) | (Vertex z) | (No contra) = No (notRightRight contra)

          hasDirectEdge value b (Connect x y) | (Vertex value) | (Yes Refl) | Empty = No (leftIsEmpty)
          hasDirectEdge value b (Connect x y) | (Vertex value) | (Yes Refl) | (Overlay left right) = No (leftIsOverlay)
          hasDirectEdge value b (Connect x y) | (Vertex value) | (Yes Refl) | (Connect left right) = No (leftIsConnect)

        hasDirectEdge a b (Connect x y) | (Vertex value) | (No contra) = No (notRightLeft contra)

      hasDirectEdge a b (Connect x y) | Empty = No (rightIsEmpty)
      hasDirectEdge a b (Connect x y) | (Overlay left right) = No (rightIsOverlay)
      hasDirectEdge a b (Connect x y) | (Connect left right) = No (rightIsConnect)



  namespace HeirarchConnect
    ||| Proof that a Connect with a heirarchical l and r graph has a connection.
    data HasOverlayConnectEdge : EdgeProof type where
      IsConnectEdge : HasVertex a l
                   -> HasVertex b r
                   -> HasOverlayConnectEdge a b (Connect l r)
      IsOverlayL : HasOverlayConnectEdge a b l -> HasOverlayConnectEdge a b (Overlay l r)
      IsOverlayR : HasOverlayConnectEdge a b r -> HasOverlayConnectEdge a b (Overlay l r)

    isEmpty : HasOverlayConnectEdge a b Empty -> Void
    isEmpty (IsConnectEdge _ _) impossible
    isEmpty (IsOverlayL _) impossible
    isEmpty (IsOverlayR _) impossible

    isVertex : HasOverlayConnectEdge a b (Vertex value) -> Void
    isVertex (IsConnectEdge _ _) impossible
    isVertex (IsOverlayL _) impossible
    isVertex (IsOverlayR _) impossible

    notLeftNotRight : (contra : HasOverlayConnectEdge a b left -> Void) -> (f : HasOverlayConnectEdge a b right -> Void) -> HasOverlayConnectEdge a b (Overlay left right) -> Void
    notLeftNotRight contra f (IsOverlayL x) = contra x
    notLeftNotRight contra f (IsOverlayR x) = f x

    notLeft : (contra : HasVertex a left -> Void) -> HasOverlayConnectEdge a b (Connect left right) -> Void
    notLeft contra (IsConnectEdge x y) = contra x

    notRight : (contra : HasVertex b right -> Void) -> HasOverlayConnectEdge a b (Connect left right) -> Void
    notRight contra (IsConnectEdge x y) = contra y

    hasOverlayConnectEdge : DecEq type => (a,b : type) -> (graph : Graph type) -> Dec (HasOverlayConnectEdge a b graph)
    hasOverlayConnectEdge a b Empty = No isEmpty
    hasOverlayConnectEdge a b (Vertex value) = No isVertex
    hasOverlayConnectEdge a b (Overlay left right) with (hasOverlayConnectEdge a b left)
      hasOverlayConnectEdge a b (Overlay left right) | (Yes prf) = Yes (IsOverlayL prf)
      hasOverlayConnectEdge a b (Overlay left right) | (No contra) with (hasOverlayConnectEdge a b right)
        hasOverlayConnectEdge a b (Overlay left right) | (No contra) | (Yes prf) = Yes (IsOverlayR prf)
        hasOverlayConnectEdge a b (Overlay left right) | (No contra) | (No f) = No (notLeftNotRight contra f)


    hasOverlayConnectEdge a b (Connect left right) with (hasVertex a left)
      hasOverlayConnectEdge a b (Connect left right) | (Yes prf) with (hasVertex b right)
        hasOverlayConnectEdge a b (Connect left right) | (Yes prf) | (Yes x) = Yes (IsConnectEdge prf x)
        hasOverlayConnectEdge a b (Connect left right) | (Yes prf) | (No contra) = No (notRight contra)

      hasOverlayConnectEdge a b (Connect left right) | (No contra) = No (notLeft contra)


  data HasEdge : EdgeProof type where
    IsDirect  : HasDirectEdge a b g -> HasEdge a b g
    IsConnect : HasOverlayConnectEdge a b g -> HasEdge a b g

  notDirectNorConnect : (f : HasOverlayConnectEdge a b graph -> Void) -> (contra : HasDirectEdge a b graph -> Void) -> HasEdge a b graph -> Void
  notDirectNorConnect f contra (IsDirect x) = contra x
  notDirectNorConnect f contra (IsConnect x) =  f x

  hasEdge : DecEq type => (a,b : type) -> (graph : Graph type) -> Dec (HasEdge a b graph)
  hasEdge a b graph with (hasDirectEdge a b graph)
    hasEdge a b graph | (Yes prf) = Yes (IsDirect prf)
    hasEdge a b graph | (No contra) with (hasOverlayConnectEdge a b graph)
      hasEdge a b graph | (No contra) | (Yes prf) = Yes (IsConnect prf)
      hasEdge a b graph | (No contra) | (No f) = No (notDirectNorConnect f contra)
