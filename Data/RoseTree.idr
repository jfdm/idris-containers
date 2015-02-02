||| Rose Trees
module Data.RoseTree

%access public

||| A Rose tree.
data Tree : Type -> Type where
  Node : a -> List (Tree a) -> Tree a


||| Syntactic Sugar.
Forest : Type -> Type
Forest a = Tree a

-- --------------------------------------------------------------- [ Instances ]

mutual
  treeMap : (a->b) -> Tree a -> Tree b
  treeMap f (Node v cs) = assert_total $ Node (f v) (map (\x => treeMap f x) cs)

  instance Functor (Tree) where
    map f tree = treeMap f tree

mkTree : a -> Tree a
mkTree val = Node val Nil

-- --------------------------------------------------------------------- [ EOF ]
