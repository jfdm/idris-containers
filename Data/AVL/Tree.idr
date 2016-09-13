-- ---------------------------------------------------------------- [ Tree.idr ]
-- Module    : Tree.idr
-- Copyright : (c) 2015,2016 See CONTRIBUTORS.md
-- License   : see LICENSE
-- --------------------------------------------------------------------- [ EOH ]
||| A Dependently Typed Implementation of an AVL Tree optimised for
||| Dictionaries.
|||
||| This code is dervied from an original design by David
||| Christiansen.
|||
||| *Note* When using this Data Structure, the design is such that the
||| tree does not factor in unbalanced trees and so removal of items
||| is not permited.
module Data.AVL.Tree

%default total
%access export

-- ------------------------------------------------------------- [ Definitions ]
data Balance : Nat -> Nat -> Type where
  LHeavy   : Balance (S n) n
  RHeavy   : Balance n     (S n)
  Balanced : Balance n     n

%name Balance b, bal

||| Indirection ensures that it reduces to at least S n' without
||| needing to case split on balance.
|||
||| Should make proofs easier.
height : Balance n m -> Nat
height b = S (height' b)
  where
    height' : Balance n m -> Nat
    height' (LHeavy {n}) = S n
    height' (RHeavy {n}) = S n
    height' {n} (Balanced {n}) = n

||| The core tree key-value data structure used to represent an AVL
||| Tree.
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
data Tree : (keyTy : Type)
         -> (valTy : Type)
         -> Type
  where
    ||| An empty Tree node.
    Empty : Tree k v

    ||| A Key Value node in the Tree.
    |||
    ||| @key   The key.
    ||| @val   The value associated with the key.
    ||| @left  The left child of the Node
    ||| @right THe right child of the Node.
    Node : (key   : k)
        -> (val   : v)
        -> (left  : Tree k v)
        -> (right : Tree k v)
        -> Tree k v

%name Tree t, tree

||| Encoding of the AVL tree height invariants.
|||
||| @height The height of a Tree.
||| @tree   The tree whose height we are capturing.
public export
data AVLInvariant : (height : Nat)
                 -> (tree   : Tree k v)
                 -> Type
  where
    ||| A tree of height zero.
    AVLEmpty : AVLInvariant 0 Empty
    ||| A Balanced tree.
    |||
    ||| @left  The invariant of the left child.
    ||| @right The invariant of the right child.
    ||| @b     The encoding of the nodes' balance.
    AVLNode : (left  : AVLInvariant n l)
           -> (right :  AVLInvariant m r)
           -> (b : Balance n m)
           -> AVLInvariant (height b) (Node k v l r)

%name AVLInvariant inv

||| An AVL Tree.
|||
||| Modelled using subset to separate the invariants from the tree
||| implementation itself.
|||
||| @height  The height of the Tree.
||| @keyTy   The type associated with the keys.
||| @valueTy The type associated with the values.
public export
AVLTree : (height  : Nat)
       -> (keyTy   : Type)
       -> (valueTy : Type)
       -> Type
AVLTree n k v = Subset (Tree k v) (AVLInvariant n)

-- --------------------------------------------------------------- [ Rotations ]
private
data InsertRes : Nat -> (k : Type) -> Type -> Type where
  Same : AVLTree n k v     -> InsertRes n k v
  Grew : AVLTree (S n) k v -> InsertRes n k v

%name InsertRes res, r

||| Process the result of an insertion of a new Key-Value pair into
||| the Tree, returning the new tree and proof of the new tree's
||| height.
|||
||| `InsertRes` is obtained from the result of running `Tree.insert`.
private
runInsertRes : InsertRes n k v -> (n : Nat ** AVLTree n k v)
runInsertRes (Same t) = (_ ** t)
runInsertRes (Grew t) = (_ ** t)

||| Perform a Left roation.
private
rotLeft : k
       -> v
       -> AVLTree n k v
       -> AVLTree (S (S n)) k v
       -> InsertRes (S (S n)) k v
-- Impossible because Empty has depth 0 and we know the depth is at least 2 from the type
rotLeft key val l (Element Empty AVLEmpty) impossible

rotLeft key val (Element l invl) (Element (Node key' val' rl rr) (AVLNode invrl invrr Balanced)) =
    Grew $ Element (Node key' val' (Node key val l rl) rr)
                        (AVLNode (AVLNode invl invrl RHeavy) invrr LHeavy)

rotLeft key val (Element l invl) (Element (Node key' val' (Node key'' val'' rll rlr) rr) (AVLNode (AVLNode invrll invrlr LHeavy) invrr LHeavy)) =
    Same $ Element (Node key'' val'' (Node key val l rll) (Node key' val' rlr rr)) -- Needs Checking
                   (AVLNode (AVLNode invl invrll Balanced) (AVLNode invrlr invrr RHeavy) Balanced)

rotLeft key val (Element l invl) (Element (Node key' val' (Node key'' val'' rll rlr) rr) (AVLNode (AVLNode invrll invrlr RHeavy) invrr LHeavy)) =
    Same $ Element (Node key'' val'' (Node key val l rll) (Node key' val' rlr rr))
                   (AVLNode (AVLNode invl invrll LHeavy) (AVLNode invrlr invrr Balanced) Balanced)

rotLeft key val (Element l invl) (Element (Node key' val' (Node key'' val'' rll rlr) rr) (AVLNode (AVLNode invrll invrlr Balanced) invrr LHeavy)) =
    Same $ Element (Node key'' val'' (Node key val l rll) (Node key' val' rlr rr))
                   (AVLNode (AVLNode invl invrll Balanced) (AVLNode invrlr invrr Balanced) Balanced) -- Needs Checking

rotLeft key val (Element l invl) (Element (Node key' val' rl rr) (AVLNode invrl invrr RHeavy)) =
    Same $ Element (Node key' val' (Node key val l rl) rr)
                   (AVLNode (AVLNode invl invrl Balanced) invrr Balanced)

||| Perform a Right rotation.
private
rotRight : k
        -> v
        -> AVLTree (S (S n)) k v
        -> AVLTree n k v
        -> InsertRes (S (S n)) k v
rotRight key val (Element Empty AVLEmpty) r impossible

rotRight key'' val'' (Element (Node key val ll (Node key' val' lrl lrr))
             (AVLNode invll (AVLNode invlrl invlrr RHeavy) RHeavy)) (Element r invr) =
  Same $ Element (Node key' val' (Node key val ll lrl) (Node key'' val'' lrr r))
                 (AVLNode (AVLNode invll invlrl LHeavy) (AVLNode invlrr invr Balanced) Balanced)

rotRight key'' val'' (Element (Node key val ll (Node key' val' lrl lrr))
             (AVLNode invll (AVLNode invlrl invlrr LHeavy) RHeavy)) (Element r invr) =
  Same $ Element (Node key' val' (Node key val ll lrl) (Node key'' val'' lrr r))
                 (AVLNode (AVLNode invll invlrl Balanced) (AVLNode invlrr invr RHeavy) Balanced)

rotRight key val (Element (Node key' val' ll lr) (AVLNode invll invlr Balanced)) (Element r invr) =
  Grew $ Element (Node key' val' ll (Node key val lr r))
                 (AVLNode invll (AVLNode invlr invr LHeavy) RHeavy)

rotRight key val (Element (Node key' val' ll lr) (AVLNode invll invlr LHeavy)) (Element r invr) =
  Same $ Element (Node key' val' ll (Node key val lr r))
                 (AVLNode invll (AVLNode invlr invr Balanced) Balanced)

rotRight key val (Element (Node key' val' ll (Node key'' val'' lrl lrr))
             (AVLNode invll (AVLNode invlrl invlrr Balanced) RHeavy)) (Element r invr) =
  Same $ Element (Node key'' val'' (Node key' val' ll lrl) (Node key val lrr r))
                 (AVLNode (AVLNode invll invlrl Balanced) (AVLNode invlrr invr Balanced) Balanced)

-- --------------------------------------------------------------- [ Insertion ]

||| Perform an insertion into the tree returning the new tree wrapped
||| in a description describing the height change.
private
doInsert : (Ord k) => k
                   -> v
                   -> AVLTree n k v
                   -> InsertRes n k v
doInsert newKey newVal (Element Empty AVLEmpty) = Grew (Element (Node newKey newVal Empty Empty)
                                                              (AVLNode AVLEmpty AVLEmpty Balanced))
doInsert newKey newVal (Element (Node key val l r) (AVLNode invl invr b)) with (compare newKey key)
  doInsert newKey newVal (Element (Node key val l r) (AVLNode invl invr b)) | EQ = Same (Element (Node newKey newVal l r) (AVLNode invl invr b))

  doInsert newKey newVal (Element (Node key val l r) (AVLNode invl invr b)) | LT with (assert_total $ doInsert newKey newVal (Element l invl))
    -- Totality checker not clever enough to see that this is smaller
    doInsert newKey newVal (Element (Node key val l r) (AVLNode invl invr b))        | LT | (Same (Element l' invl'))
                                                                                          = Same $ Element (Node key val l' r) (AVLNode invl' invr b)
    doInsert newKey newVal (Element (Node key val l r) (AVLNode invl invr LHeavy))   | LT | (Grew (Element l' invl'))
                                                                                          = rotRight key val (Element l' invl') (Element r invr)
    doInsert newKey newVal (Element (Node key val l r) (AVLNode invl invr Balanced)) | LT | (Grew (Element l' invl'))
                                                                                          = Grew $ Element (Node key val l' r) (AVLNode invl' invr LHeavy)
    doInsert newKey newVal (Element (Node key val l r) (AVLNode invl invr RHeavy))   | LT | (Grew (Element l' invl'))
                                                                                          = Same $ Element (Node key val l' r) (AVLNode invl' invr Balanced)

  doInsert newKey newVal (Element (Node key val l r) (AVLNode invl invr b)) | GT with (assert_total $ doInsert newKey newVal (Element r invr))
  -- Totality checker not clever enough to see that this is smaller
    doInsert newKey newVal (Element (Node key val l r) (AVLNode invl invr b))        | GT | (Same (Element r' invr'))
                                                                                          = Same $ Element (Node key val l r') (AVLNode invl invr' b)
    doInsert newKey newVal (Element (Node key val l r) (AVLNode invl invr LHeavy))   | GT | (Grew (Element r' invr'))
                                                                                          = Same $ Element (Node key val l r') (AVLNode invl invr' Balanced)
    doInsert newKey newVal (Element (Node key val l r) (AVLNode invl invr Balanced)) | GT | (Grew (Element r' invr'))
                                                                                          = Grew $ Element (Node key val l r') (AVLNode invl invr' RHeavy)
    doInsert newKey newVal (Element (Node key val l r) (AVLNode invl invr RHeavy))   | GT | (Grew (Element r' invr'))
                                                                                          = rotLeft key val (Element l invl) (Element r' invr')


-- --------------------------------------- [ Public API for working with Trees ]

||| Insert a key value pair into the tree, returning a the new tree
||| and possibly its new height.
insert : Ord k => k -> v -> AVLTree n k v -> (n : Nat ** AVLTree n k v)
insert k v t = runInsertRes (doInsert k v t)


||| Find a value in the tree.
lookup : (Ord k) => k -> AVLTree h k v -> Maybe v
lookup key (Element t _) = lookup' key t
  where
    lookup' : (Ord k) => k -> Tree k v -> Maybe v
    lookup' key Empty = Nothing
    lookup' key (Node key' value' l r) with (compare key key')
      lookup' key (Node key' value' l r) | LT = lookup' key l
      lookup' key (Node key' value' l r) | EQ = Just value'
      lookup' key (Node key' value' l r) | GT = lookup' key r

||| Update an element in the tree.
update : (Ord k) => k
                 -> (v -> v)
                 -> AVLTree h k v
                 -> AVLTree h k v
update key f t@(Element Empty inv) = t
update key f (Element (Node key' value' l r) inv) with (compare key key')
    update key f (Element (Node key' value' l r) (AVLNode invl invr b)) | LT with (assert_total $ update key f (Element l invl)) -- Totality checker again
      update key f (Element (Node key' value' l r) (AVLNode invl invr b)) | LT | (Element l' invl')
                                                           = Element (Node key' value' l' r) (AVLNode invl' invr b)
    update key f (Element (Node key' value' l r) (AVLNode invl invr b)) | EQ
                                                           = Element (Node key' (f value') l r) (AVLNode invl invr b)
    update key f (Element (Node key' value' l r) (AVLNode invl invr b)) | GT with (assert_total $ update key f (Element r invr))
      update key f (Element (Node key' value' l r) (AVLNode invl invr b)) | GT | (Element r' invr')
                                                           = Element (Node key' value' l r') (AVLNode invl invr' b)

||| Perform a right fold over the tree.
foldr : (step : k -> v -> p -> p)
     -> (init : p)
     -> AVLTree n k v
     -> p
foldr step init (Element t _) = foldr' step init t
  where
    foldr' : (k -> v -> p -> p) -> p -> Tree k v -> p
    foldr' step' init' Empty = init'
    foldr' step' init' (Node key val l r) = foldr' step' (step' key val (foldr' step' init' r)) l

||| Construct a AVL Tree from an association list.
fromList : (Ord k) => List (k, v)
                   -> (n : Nat ** AVLTree n k v)
fromList [] = (0 ** Element Empty AVLEmpty)
fromList ((k, v) :: xs) with (doInsert k v (snd (fromList xs)))
  fromList ((k, v) :: xs) | (Same x) = (_ ** x)
  fromList ((k, v) :: xs) | (Grew x) = (_ ** x)

||| Flatten the tree to an association list.
toList : AVLTree n k v -> List (k, v)
toList = foldr (\k,v,xs => (k, v) :: xs) []

||| Is the tree empty?
isEmpty : AVLTree h k v -> Bool
isEmpty (Element t _) = isEmpty' t
  where
    isEmpty' : Tree k v -> Bool
    isEmpty' Empty          = True
    isEmpty' (Node _ _ _ _) = False

||| Calculate the size of the tree.
size : AVLTree h k v -> Nat
size = foldr (\_,_=> S) 0

||| Return a list of keys in the tree.
keys : AVLTree h k v -> List k
keys = map fst . toList

||| Return a list of the values in the key.
values : AVLTree h k v -> List v
values = map snd . toList

||| Check if the provided check holds for all elements in the tree.
all : (pred : k -> v -> Bool) ->  AVLTree h k v -> Bool
all pred = foldr (\k,v,pred' => pred' && pred k v) True

||| Check if the provided check holds for at least one element in the tree.
any : (pred : k -> v -> Bool) ->  AVLTree h k v -> Bool
any pred = foldr (\k,v,pred' => pred' || pred k v) False

||| Does the given key exist in the tree?
hasKey : (o : Ord k) => k -> AVLTree h k v -> Bool
hasKey key = any (\key',value' => key == key')

||| Does the given value exist in the tree?
hasValue : (Eq v) => v -> AVLTree h k v -> Bool
hasValue value = any (\key',value' => value == value')

||| Find the first key that satisfies the provided predicate.
findKey : (pred : v -> Bool) -> AVLTree h k v -> Maybe k
findKey pred = foldr (\k,v,p => if pred v then Just k else p) Nothing

||| Find the key that is associated with provided value.
findKeyOf : (Eq v) => v -> AVLTree h k v -> Maybe k
findKeyOf value = findKey (== value)

-- --------------------------------------------------------- [ Implementations ]
private
eqTree : (Eq k, Eq v) => Tree k v -> Tree k v -> Bool
eqTree Empty              Empty              = True
eqTree (Node xk xv xl xr) (Node yk yv yl yr) =
      xk == yk  &&
      xv == yv  &&
      eqTree xl yl &&
      eqTree xr yr
eqTree _ _                                   = False

(Eq k, Eq v) => Eq (Tree k v) where
  (==) x y = eqTree x y

(Eq k, Eq v) => Eq (AVLTree h k v) where
  (==) (Element t _) (Element t' _) = t == t'

(Show k, Show v) => Show (Tree k v) where
  show Empty          = ""
  show (Node k v l r) = unwords
      [
        "{"
      , show l
      , "(", show k, ":", show v, "),"
      , show r
      , "}"
      ]

(Show k, Show v) => Show (AVLTree h k v) where
  show (Element t _) = show t
-- --------------------------------------------------------------------- [ Key ]

||| A proof that some key is found in a Tree
public export
data Key : k -> Tree k v -> Type where
  Here : Key key (Node key _ _ _)
  InRight : (later : Key key r) -> Key key (Node _ _ _ r)
  InLeft : (later : Key key l) -> Key key (Node _ _ l _)

||| A wrapper to be used with AVLTree
public export
AVLKey : k -> AVLTree h k v -> Type
AVLKey key avl = Key key (getWitness avl)

||| An empty tree has no key
noEmptyKey : {key : k} -> Key key Empty -> Void
noEmptyKey Here impossible
noEmptyKey (InRight _) impossible
noEmptyKey (InLeft _) impossible

Uninhabited (Key key Empty) where
  uninhabited = noEmptyKey

||| An item that is not in the root, not in the left child and not in the
||| right child is not in the Tree at all
noKeyFound : {key : k} -> {val : v}
          -> {key' : k} -> {l : Tree k v} -> {r : Tree k v}
          -> Not (key = key') -> Not (Key key l) -> Not (Key key r) 
          -> Not (Key key (Node key' val l r))
noKeyFound notHere notInLeft notInRight Here = notHere Refl
noKeyFound notHere notInLeft notInRight (InLeft later) = notInLeft later
noKeyFound notHere notInLeft notInRight (InRight later) = notInRight later

||| A decision procedure for Key
isKey : DecEq k => (key : k) -> (tree : Tree k v) -> Dec (Key key tree)
isKey key Empty = No noEmptyKey
isKey key (Node key' _ l r) with (decEq key key')
  isKey key (Node key  _ l r) | (Yes Refl) = Yes Here
  isKey key (Node key' _ l r) | (No notHere) with (isKey key l)
    isKey key (Node key' _ l r) | (No notHere) | (Yes inLeft) = Yes (InLeft inLeft)
    isKey key (Node key' _ l r) | (No notHere) | (No notInLeft) with (isKey key r)
      isKey key (Node key' _ l r) | (No notHere) | (No notInLeft) | (Yes inRight) = Yes (InRight inRight)
      isKey key (Node key' _ l r) | (No notHere) | (No notInLeft) | (No notInRight) = No (noKeyFound notHere notInLeft notInRight)

-- --------------------------------------------------------------------- [ EOF ]
