module Data.AVL.Core.API

import public Data.Tree
import public Data.AVL.Core

%default total
%access export

namespace AVL
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
  (==) = eqTree

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
