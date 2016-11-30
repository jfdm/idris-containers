-- ------------------------------------------------------------ [ RoseTree.idr ]
-- Module    : RoseTree.idr
-- Copyright : (c) 2015,2016 See CONTRIBUTORS.md
-- License   : see LICENSE
-- --------------------------------------------------------------------- [ EOH ]

||| Trees with unbounded number of children
module Data.RoseTree

%default total
%access export

||| A RTree.
data RTree : Type -> Type where
  Empty : RTree a
  Node : (value : a) -> (children : List (RTree a)) -> RTree a

contains : Eq a => a -> RTree a -> Bool
contains x Empty       = False
contains x (Node y cs) =
    if x == y
      then True
      else doChildren x cs
  where
    doChildren : Eq a => a -> List (RTree a) -> Bool
    doChildren a Nil     = False
    doChildren a (Empty :: xs)    = doChildren a xs
    doChildren a (Node a' ys::xs) = a == a' || (doChildren a ys || doChildren a xs )

data HasValue : RTree a -> a -> Type where
  DoesHaveValue : HasValue (Node p cs) n

private
noValueEmpty : HasValue (Empty) x -> Void
noValueEmpty DoesHaveValue impossible

||| Insert into a Rose RTree
|||
||| //TODO Make total
partial
insert : Eq a => (value : a) -> (parent : Maybe a) -> (tree : RTree a) -> RTree a
insert x Nothing  (Empty)      = Node x Nil
insert x Nothing  (Node y xs)  = Node y (Node x Nil:: xs)
insert x (Just p) (Empty)      = Node p [Node x Nil]
insert x (Just p) (Node y cs)  =
    if p == y
      then Node y (Node x Nil :: cs)
      else Node y $ map (\y => insert x (Just p) y) cs
