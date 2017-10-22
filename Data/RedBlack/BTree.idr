-- --------------------------------------------------------------- [ BTree.idr ]
-- Module    : BTree.idr
-- Copyright : (c) 2017 See CONTRIBUTORS.md
-- License   : see LICENSE
-- --------------------------------------------------------------------- [ EOH ]
||| Implementation of a Binary Tree as a Red-Black Binary Search Tree.
|||
||| The underlying Red-Black Tree is a Key-Value Tree, this library
||| just wraps this up as a simple Binary tree for values i.e. keys.
module Data.RedBlack.BTree

import Data.RedBlack.Tree

%default total
%access export

-- ------------------------------------------------------------- [ Definitions ]

||| A Binary Search Tree.
|||
||| @ty The type of the elements in the tree.
data BTree : (ty : Type) -> Type
    where
      MkTree : {a : Type} -> RBTree n B a Unit -> BTree a

-- --------------------------------------------------------------------- [ API ]

||| Return an empty BTree.
empty : Ord a => BTree a
empty = MkTree empty

||| Insert an element into the Tree.
insert : (Ord a) => a -> BTree a -> BTree a
insert a (MkTree t) = case Tree.insert a () t of
  (_ ** t') => MkTree t'

||| Does the tree contain the given element?
contains : (Ord a) => a -> BTree a -> Bool
contains a (MkTree t) = isJust (Tree.lookup a t)

||| How many nodes are in the tree?
size : BTree a -> Nat
size (MkTree t) = Tree.size t

||| Construct an ordered list containing the elements of the tree.
toList : BTree a -> List a
toList (MkTree t) = map fst $ Tree.toList t

||| Construct a tree from a list of elements.
fromList : (Ord a) => List a -> BTree a
fromList xs = (foldl (\t,k => BTree.insert k t) empty xs)

-- --------------------------------------------------------------- [ Instances ]

Foldable BTree where
  foldr f i (MkTree t) = foldr (\x,_,p => f x p) i t

-- Eq a => Eq (BTree a) where
--   (==) (MkTree t) (MkTree t') = t == t'

Show a => Show (BTree a) where
  show s = "{ " ++ (unwords . intersperse "," . map show . BTree.toList $ s) ++ " }"

-- --------------------------------------------------------------------- [ EOF ]
