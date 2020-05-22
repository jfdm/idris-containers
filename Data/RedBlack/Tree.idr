-- ------------------------------------------------------ [ Tree.idr<RedBlack> ]
-- Module    : Tree.idr
-- License   : see LICENSE
-- --------------------------------------------------------------------- [ EOH ]
-- http://www.cs.kent.ac.uk/people/staff/smk/redblack/Untyped.hs
module Data.RedBlack.Tree

import Debug.Error
%language ElabReflection

%default total
%access export

-- ------------------------------------------------------------- [ Definitions ]
public export
data Colour = R | B

||| The core tree key-value data structure used to represent an
||| Red-Black Tree.
|||
||| This structure doesn't encode the invariants of the tree and is
||| *simply* a container. This structure ideally shouldn't be exposed
||| to the user at all. This structure should be used to build other
||| data structures.  See the modules alongside this for appropriate
||| interfaces for using the tree.
|||
||| @keyTy The type associated with the key.
||| @valTy The type associated with the value.
public export
data Tree : (colour : Colour)
         -> (keyTy : Type)
         -> (valTy : Type)
         -> Type
  where
    ||| An empty Tree node.
    Empty : Tree B k v

    ||| A Key Value node in the Tree.
    |||
    ||| @key   The key.
    ||| @val   The value associated with the key.
    ||| @left  The left child of the Node
    ||| @right THe right child of the Node.
    Node : (c3 : Colour)
        -> (key   : k)
        -> (val   : v)
        -> (left  : Tree c1 k v)
        -> (right : Tree c2 k v)
        -> Tree c3 k v

%name Tree t, tree

public export
data RBInvariant : (blackHeight : Nat)
                -> (colour : Colour)
                -> (valid : Bool)
                -> (tree : Tree colour k v)
                -> Type
  where
    ||| A tree of height zero.
    RBEmpty : RBInvariant 0 B True Empty
    ||| A balanced black tree.
    |||
    ||| @left  The invariant of the left child.
    ||| @right The invariant of the right child.
    BNode : (left  : RBInvariant n _ True l)
         -> (right : RBInvariant n _ True r)
         -> RBInvariant (S n) B True (Node B k v l r)
    ||| A balanced red tree.
    |||
    ||| @left  The invariant of the left child.
    ||| @right The invariant of the right child.
    RNode : (left  : RBInvariant n B True l)
         -> (right : RBInvariant n B True r)
         -> RBInvariant n R True (Node R k v l r)

    ||| A red tree with a red left child.
    |||
    ||| @left  The invariant of the left child.
    ||| @right The invariant of the right child.
    LBad : (left  : RBInvariant n R True l)
        -> (right : RBInvariant n B True r)
        -> RBInvariant n R False (Node R k v l r)

    ||| A red tree with a red right child.
    |||
    ||| @left  The invariant of the left child.
    ||| @right The invariant of the right child.
    RBad : (left  : RBInvariant n B True l)
        -> (right : RBInvariant n R True r)
        -> RBInvariant n R False (Node R k v l r)

%name RBInvariant inv

||| An Red-Black Tree.
|||
||| Modelled using subset to separate the invariants from the tree
||| implementation itself.
|||
||| @blackHeight  The height of the Tree.
||| @keyTy        The type associated with the keys.
||| @valueTy      The type associated with the values.
public export
RBTree : (blackHeight  : Nat)
      -> (colour : Colour)
      -> (keyTy   : Type)
      -> (valueTy : Type)
      -> Type
RBTree n c k v = Subset (Tree c k v) (RBInvariant n c True)

private
InsTree : (blackHeight  : Nat)
       -> (colour : Colour)
       -> (keyTy   : Type)
       -> (valueTy : Type)
       -> (valid : Bool)
       -> Type
InsTree n c k v valid = Subset (Tree c k v) (RBInvariant n c valid)

-- --------------------------------------------------------------- [ Insertion ]

private
balance : k -> v -> RBTree n c1 k v -> RBTree n c2 k v -> (c3 ** RBTree (S n) c3 k v)
balance {n} y vy (Element (Node _ x vx a b) (RNode pf_l_l pf_l_r))
                 (Element (Node _ z vz c d) (RNode pf_r_l pf_r_r)) =
  let t = (Node R y vy (Node B x vx a b) (Node B z vz c d))
      pf = RNode (BNode pf_l_l pf_l_r) (BNode pf_r_l pf_r_r)
  in (R ** Element t pf)
balance {n} x vx (Element a pf_a) (Element b pf_b) =
  let t = (Node B x vx a b)
      pf = BNode pf_a pf_b
  in (B ** Element t pf)

private
recolorRight : (Ord k) => k -> v -> RBTree n c k v -> InsTree n R k v False -> (c' ** valid ** InsTree (S n) c' k v valid)

recolorRight g vg (Element (Node R u vu t5 t4) (RNode pf_5 pf_4))
                  (Element (Node R p vp t3 tn) (RBad pf_3 pf_n)) =
  (R ** True ** Element (Node R g vg (Node B u vu t5 t4) (Node B p vp t3 tn))
                        (RNode (BNode pf_5 pf_4) (BNode pf_3 pf_n)))

recolorRight g vg (Element (Node R u vu t5 t4) (RNode pf_5 pf_4))
                  (Element (Node R p vp tn t3) (LBad pf_n pf_3)) =
  (R ** True ** Element (Node R g vg (Node B u vu t4 t5) (Node B p vp tn t3))
                        (RNode (BNode pf_4 pf_5) (BNode pf_n pf_3)))

recolorRight g vg (Element (Node B u vu t5 t4) (BNode pf_5 pf_4))
                  (Element (Node R p vp t3 (Node R n vn t2 t1)) (RBad pf_3 (RNode pf_2 pf_1))) =
  (B ** True ** Element (Node B p vp (Node R g vg (Node B u vu t5 t4) t3)
                                     (Node R n vn t2 t1))
                        (BNode (RNode (BNode pf_5 pf_4) pf_3) (RNode pf_2 pf_1)))

recolorRight g vg (Element Empty RBEmpty)
                  (Element (Node R p vp t3 (Node R n vn t2 t1)) (RBad pf_3 (RNode pf_2 pf_1))) =
  (B ** True ** Element (Node B p vp (Node R g vg Empty t3)
                                     (Node R n vn t2 t1))
                        (BNode (RNode RBEmpty pf_3) (RNode pf_2 pf_1)))

recolorRight g vg (Element (Node B u vu t5 t4) (BNode pf_5 pf_4))
                  (Element (Node R p vp (Node R n vn t3 t2) t1) (LBad (RNode pf_3 pf_2) pf_1)) =
  (B ** True ** Element (Node B n vn (Node R g vg (Node B u vu t5 t4) t3)
                                     (Node R p vp t2 t1))
                        (BNode (RNode (BNode pf_5 pf_4) pf_3) (RNode pf_2 pf_1)))

recolorRight g vg (Element Empty RBEmpty)
                  (Element (Node R p vp (Node R n vn t3 t2) t1) (LBad (RNode pf_3 pf_2) pf_1)) =
  (B ** True ** Element (Node B n vn (Node R g vg Empty t3)
                                     (Node R p vp t2 t1))
                        (BNode (RNode RBEmpty pf_3) (RNode pf_2 pf_1)))

private
recolorLeft : (Ord k) => k -> v -> InsTree n R k v False -> RBTree n c k v -> (c' ** valid ** InsTree (S n) c' k v valid)

recolorLeft g vg (Element (Node R p vp tn t3) (LBad pf_n pf_3))
                 (Element (Node R u vu t4 t5) (RNode pf_4 pf_5)) =
  (R ** True ** Element (Node R g vg (Node B p vp tn t3)
                                     (Node B u vu t4 t5))
                        (RNode (BNode pf_n pf_3) (BNode pf_4 pf_5)))

recolorLeft g vg (Element (Node R p vp t1 tn) (RBad pf_1 pf_n))
                 (Element (Node R u vu t4 t5) (RNode pf_4 pf_5)) =
  (R ** True ** Element (Node R g vg (Node B p vp t1 tn)
                                     (Node B u vu t4 t5))
                        (RNode (BNode pf_1 pf_n) (BNode pf_4 pf_5)))

recolorLeft g vg (Element (Node R p vp (Node R n vn t1 t2) t3) (LBad (RNode pf_1 pf_2) pf_3))
                 (Element (Node B u vu t4 t5) (BNode pf_4 pf_5)) =
  (B ** True ** Element (Node B p vp (Node R n vn t1 t2)
                                     (Node R g vg t3 (Node B u vu t4 t5)))
                        (BNode (RNode pf_1 pf_2) (RNode pf_3 (BNode pf_4 pf_5))))

recolorLeft g vg (Element (Node R p vp (Node R n vn t1 t2) t3) (LBad (RNode pf_1 pf_2) pf_3))
                 (Element Empty RBEmpty) =
  (B ** True ** Element (Node B p vp (Node R n vn t1 t2)
                                     (Node R g vg t3 Empty))
                        (BNode (RNode pf_1 pf_2) (RNode pf_3 RBEmpty)))

recolorLeft g vg (Element (Node R p vp t1 (Node R n vn t2 t3)) (RBad pf_1 (RNode pf_2 pf_3)))
                 (Element (Node B u vu t4 t5) (BNode pf_4 pf_5)) =
  (B ** True ** Element (Node B n vn (Node R p vp t1 t2)
                                     (Node R g vg t3 (Node B u vu t4 t5)))
                        (BNode (RNode pf_1 pf_2) (RNode pf_3 (BNode pf_4 pf_5))))

recolorLeft g vg (Element (Node R p vp t1 (Node R n vn t2 t3)) (RBad pf_1 (RNode pf_2 pf_3)))
                 (Element Empty RBEmpty) =
  (B ** True ** Element (Node B n vn (Node R p vp t1 t2)
                                     (Node R g vg t3 Empty))
                        (BNode (RNode pf_1 pf_2) (RNode pf_3 RBEmpty)))

private
ins : Ord k => k -> v -> RBTree n c k v -> (c' ** valid ** InsTree n c' k v valid)
ins x vx (Element Empty RBEmpty) = (R ** True ** Element (Node R x vx Empty Empty) (RNode RBEmpty RBEmpty))
ins x vx t@(Element (Node _ y _ _ _) _) = insWith x vx t (compare x y)
  where
    addValid : (c ** InsTree n c k v True) -> (c ** valid ** InsTree n c k v valid)
    addValid (c ** t) = (c ** True ** t)

    insWith : Ord k => k -> v -> RBTree n c k v -> Ordering -> (c' ** valid ** InsTree n c' k v valid)

    insWith x vx (Element Empty RBEmpty) _ =  -- unreachable, but make totality checker happy
      (R ** True ** Element (Node R x vx Empty Empty) (RNode RBEmpty RBEmpty))

    insWith x vx (Element n@(Node B y vy a b) pf) EQ =
      (B ** True ** Element n pf)
    insWith x vx t@(Element (Node B y vy a b) (BNode pf_a pf_b)) LT =
      let t_a = assert_smaller t (Element a pf_a)
      in case ins x vx t_a of
        (_ ** True ** t_a') => addValid (balance y vy t_a' (Element b pf_b))
        (R ** False ** t_a') => recolorLeft y vy t_a' (Element b pf_b)
        (B ** False ** (Element _ _)) impossible
    insWith x vx t@(Element (Node B y vy a b) (BNode pf_a pf_b)) GT =
      let t_b = assert_smaller t (Element b pf_b)
      in case ins x vx t_b of
        (_ ** True ** t_b') => addValid (balance y vy (Element a pf_a) t_b')
        (R ** False ** t_b') => recolorRight y vy (Element a pf_a) t_b'
        (B ** False ** (Element _ _)) impossible

    insWith x vx (Element n@(Node R y vy a b) pf) EQ =
      (R ** True ** Element n pf)
    insWith x vx t@(Element (Node R y vy a b) (RNode pf_a pf_b)) LT =
      let t_a = assert_smaller t (Element a pf_a)
      in case ins x vx t_a of
        (B ** True ** Element a' pf_a') => (R ** True ** Element (Node R y vy a' b) (RNode pf_a' pf_b))
        (R ** True ** Element a' pf_a') => (R ** False ** Element (Node R y vy a' b) (LBad pf_a' pf_b))
        (R ** False ** t_a') => error "impossible"
        (B ** False ** Element _ _) impossible
    insWith x vx t@(Element (Node R y vy a b) (RNode pf_a pf_b)) GT =
      let t_b = assert_smaller t (Element b pf_b)
      in case ins x vx t_b of
        (B ** True ** Element b' pf_b') => (R ** True ** Element (Node R y vy a b') (RNode pf_a pf_b'))
        (R ** True ** Element b' pf_b') => (R ** False ** Element (Node R y vy a b') (RBad pf_a pf_b'))
        (R ** False ** t_b') => error "impossible"
        (B ** False ** Element _ _) impossible

-- --------------------------------------- [ Public API for working with Trees ]

||| An empty tree
empty : RBTree 0 B k v
empty = Element Empty RBEmpty

||| Insert a key value pair into the tree, returning a the new tree
||| and possibly its new height.
insert : Ord k => k -> v -> RBTree n B k v -> (n' : Nat ** RBTree n' B k v)
insert x vx s =
  case ins x vx s of
    (B ** True ** t) => (_ ** t)
    (R ** True ** Element (Node R k v l r) (RNode pf_l pf_r)) =>
      (_ ** Element (Node B k v l r) (BNode pf_l pf_r))
    (B ** False ** Element _ _) impossible
    (R ** False ** Element (Node R k v l r) (RBad pf_l pf_r)) =>
      (_ ** Element (Node B k v l r) (BNode pf_l pf_r))
    (R ** False ** Element (Node R k v l r) (LBad pf_l pf_r)) =>
      (_ ** Element (Node B k v l r) (BNode pf_l pf_r))

||| Find a value in the tree.
lookup : (Ord k) => k -> RBTree n B k v -> Maybe v
lookup key (Element t _) = lookup' key t
  where
    lookup' : (Ord k) => k -> Tree c k v -> Maybe v
    lookup' key Empty = Nothing
    lookup' key (Node _ key' value' l r) with (compare key key')
      lookup' key (Node _ key' value' l r) | LT = lookup' key l
      lookup' key (Node _ key' value' l r) | EQ = Just value'
      lookup' key (Node _ key' value' l r) | GT = lookup' key r

||| Perform a right fold over the tree.
foldr : (step : k -> v -> p -> p)
     -> (init : p)
     -> RBTree n B k v
     -> p
foldr step init (Element t _) = foldr' step init t
  where
    foldr' : (k -> v -> p -> p) -> p -> Tree c k v -> p
    foldr' step' init' Empty = init'
    foldr' step' init' (Node _ key val l r) = foldr' step' (step' key val (foldr' step' init' r)) l

||| Construct a AVL Tree from an association list.
fromList : (Ord k) => List (k, v) -> (n : Nat ** RBTree n B k v)
fromList xs = go xs empty
  where go : (Ord k) => List (k, v) -> RBTree n B k v -> (n' : Nat ** RBTree n' B k v)
        go [] t = (0 ** Element Empty RBEmpty)
        go ((k, v) :: xs) t = case insert k v t of
          (_ ** t') => go xs t'

||| Flatten the tree to an association list.
toList : RBTree n B k v -> List (k, v)
toList = foldr (\k,v,xs => (k, v) :: xs) []

||| Size of the tree.
size : RBTree n B k v -> Nat
size t = Tree.foldr (\_,_,res => S res) Z t

-- --------------------------------------------------------------------- [ EOF ]
