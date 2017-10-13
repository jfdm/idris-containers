-- ------------------------------------------------------ [ Tree.idr<RedBlack> ]
-- Module    : Tree.idr
-- License   : see LICENSE
-- --------------------------------------------------------------------- [ EOH ]
-- http://www.cs.kent.ac.uk/people/staff/smk/redblack/Untyped.hs
module Data.RedBlack.Tree

%default total
%access export

-- ------------------------------------------------------------- [ Definitions ]
private
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
    Node : Colour
        -> (key   : k)
        -> (val   : v)
        -> (left  : Tree k v)
        -> (right : Tree k v)
        -> Tree k v

%name Tree t, tree

-- --------------------------------------------------------------- [ Balancing ]

private
balance : k -> v -> Tree k v -> Tree k v -> Tree k v
balance y vy (Node R x vx a              b)    (Node R z vz c d)                 = Node R y vy (Node B x vx a b) (Node B z vz c d)
balance z vz (Node R y vy (Node R x vx a b) c) d                                 = Node R y vy (Node B x vx a b) (Node B z vz c d)
balance z vz (Node R x vx a                    (Node R y vy b c)) d              = Node R y vy (Node B x vx a b) (Node B z vz c d)
balance x vx a                                 (Node R y vy b (Node R z vz c d)) = Node R y vy (Node B x vx a b) (Node B z vz c d)
balance x vx a                                 (Node R z vz (Node R y vy b c) d) = Node R y vy (Node B x vx a b) (Node B z vz c d)
balance x vx a                                 b                                 = Node B x vx a b

-- --------------------------------------------------------------- [ Insertion ]

private
ins : Ord k => k -> v -> Tree k v -> Tree k v
ins x vx Empty            = Node R x vx Empty Empty
ins x vx t@(Node B y vy a b) =
    case compare x y of
        LT => balance y vy (ins x vx a) b
        GT => balance y vy a            (ins x vx b)
        EQ => t
ins x vx t@(Node R y vy a b) =
    case compare x y of
        LT => Node R y vy (ins x vx a) b
        GT => Node R y vy a            (ins x vx b)
        EQ => t


-- --------------------------------------- [ Public API for working with Trees ]

||| An empty tree
empty : Tree k v
empty = Empty

||| Insert a key value pair into the tree, returning a the new tree
||| and possibly its new height.
insert : Ord k => k -> v -> Tree k v -> Tree k v
insert x vx s =
  case ins x vx s of
      Empty => Empty  -- imposisible, but make the totallity checker happy until we add dependent types
      Node _ z vz l r => Node B z vz l r

||| Find a value in the tree.
lookup : (Ord k) => k -> Tree k v -> Maybe v
lookup key t = lookup' key t
  where
    lookup' : (Ord k) => k -> Tree k v -> Maybe v
    lookup' key Empty = Nothing
    lookup' key (Node _ key' value' l r) with (compare key key')
      lookup' key (Node _ key' value' l r) | LT = lookup' key l
      lookup' key (Node _ key' value' l r) | EQ = Just value'
      lookup' key (Node _ key' value' l r) | GT = lookup' key r

||| Perform a right fold over the tree.
foldr : (step : k -> v -> p -> p)
     -> (init : p)
     -> Tree k v
     -> p
foldr step init n = foldr' step init n
  where
    foldr' : (k -> v -> p -> p) -> p -> Tree k v -> p
    foldr' step' init' Empty = init'
    foldr' step' init' (Node _ key val l r) = foldr' step' (step' key val (foldr' step' init' r)) l

||| Construct a AVL Tree from an association list.
fromList : (Ord k) => List (k, v)
                   -> (Tree k v)
fromList xs = foldl (flip $ uncurry insert) Empty xs

||| Flatten the tree to an association list.
toList : Tree k v -> List (k, v)
toList = foldr (\k,v,xs => (k, v) :: xs) []

size : Tree k v -> Nat
size t = Tree.foldr (\_,_,res => S res) Z t


-- --------------------------------------------------------------------- [ EOF ]
