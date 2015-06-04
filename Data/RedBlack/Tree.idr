-- http://www.cs.kent.ac.uk/people/staff/smk/redblack/Untyped.hs
module Data.RedBlack.Tree

%access public

private
data Colour = R | B

data Tree : Type -> Type where
  Empty : Tree a
  Node  : Colour -> a -> Tree a -> Tree a -> Tree a


balance : a -> Tree a -> Tree a -> Tree a
balance y (Node R x a              b) (Node R z c d) = Node R y (Node B x a b) (Node B z c d)
balance z (Node R y (Node R x a b) c) d              = Node R y (Node B x a b) (Node B z c d)
balance z (Node R x a                 (Node R y b c)) d = Node R y (Node B x a b) (Node B z c d)
balance x a                           (Node R y b (Node R z c d)) = Node R y (Node B x a b) (Node B z c d)
balance x a                           (Node R z (Node R y b c) d) = Node R y (Node B x a b) (Node B z c d)
balance x a                           b = Node B x a b

private
ins : Ord a => a -> Tree a -> Tree a
ins x Empty            = Node R x Empty Empty
ins x t@(Node B y a b) =
    case compare x y of
        LT => balance y (ins x a) b
        GT => balance y a         (ins x b)
        EQ => t
ins x t@(Node R y a b) =
    case compare x y of
        LT => Node R y (ins x a) b
        GT => Node R y a         (ins x b)
        EQ => t


contains : Ord a => a -> Tree a -> Bool
contains x Empty = False
contains x (Node _ y l r) =
  case compare x y of
    LT => contains x l
    GT => contains x r
    EQ => True


empty : Tree a
empty = Empty

insert : Ord a => a -> Tree a -> Tree a
insert x s = let Node _ z l r = ins x s in Node B z l r

toList : Tree a -> List a
toList Empty = Nil
toList (Node _ y l r) = Tree.toList l ++ [y] ++ Tree.toList r

fromList : Ord a => List a -> Tree a
fromList xs = foldl (flip $ insert) empty xs
