||| Implementation of an AVL Binary Search Tree.
|||
||| Code adapted from Haskell sources from `Data.FiniteMap` and `Data.Map`.
|||
||| For theory see:
|||
||| * Stephen Adams, 'Efficient sets: a balancing act', Journal of
||| Functional Programming 3(4):553-562, October 1993,
||| http://www.swiss.ai.mit.edu/~adams/BB/.
||| * J. Nievergelt and E.M. Reingold, 'Binary search trees of bounded
||| balance', SIAM journal of computing 2(1), March 1973.
module Data.AVL.Tree

-- @TODO Add dependent type and algebraic effect features to shore up
-- implementation.
--- @TODO Add complexity documentation.

%access public
--%default total

-- -------------------------------------------------------------- [ Definition ]
||| An AVL Tree.
|||
||| @a The element type.
data AVLTree : (a : Type) -> Type where
  Empty : AVLTree a
  Node : Nat -> a -> AVLTree a -> AVLTree a -> AVLTree a

private
height : AVLTree a -> Nat
height Empty           = Z
height (Node d a l r) = d

private
mkNode : a
       -> AVLTree a
       -> AVLTree a
       -> AVLTree a
mkNode e l r = Node (1+h) e l r
  where
    h : Nat
    h = max (height l) (height r)

avlIsEmpty : AVLTree e -> Bool
avlIsEmpty Empty = True
avlIsEmpty _    = False

-- ---------------------------------------------------------------- [ Rotation ]
private
bias : AVLTree a -> Nat
bias (Node _ _ l r)  = height l - height r
bias Empty           = 0

private
data ROTDIR = RotRL | RotRLB | RotLR | RotLRB | NOUT

private
rotDIR : AVLTree a -> AVLTree a -> ROTDIR
rotDIR l r = if (hr + 1 < hl) && (bias l < 0)
    then RotRLB
    else if (hr + 1 < hl)
      then RotRL
      else if (hl + 1 < hr) && (0 < bias r)
        then RotLRB
        else if (hl + 1 < hr)
          then RotLR
          else NOUT
  where
    hl : Nat
    hl = height l
    hr : Nat
    hr = height r

private
rotr : AVLTree a -> AVLTree a
rotr Empty             = Empty
rotr (Node _ e l r)   with (l)
   | (Node _ e' l' r')  = mkNode e l' (mkNode e' r r' )
   | Empty              = mkNode e l r
-- 'missing case' Empty might cause jip

private
rotl : AVLTree a -> AVLTree a
rotl Empty             = Empty
rotl (Node _ e l r) with (r)
  | (Node _ e' l' r') = mkNode e' (mkNode e l l') r'
  | Empty             = mkNode e l r

-- 'missing case 'Empty might cause jip

-- --------------------------------------------------------------- [ Balancing ]

private
balance : a -> AVLTree a -> AVLTree a -> Ordering -> AVLTree a
balance e l r o = case rotDIR l r o of
     RotRLB => rotr $ mkNode e (rotl l) r
     RotRL  => rotr $ mkNode e l r
     RotLRB => rotl $ mkNode e l $ rotr r
     RotLR  => rotl $ mkNode e l r
     NOUT   => mkNode e l r

-- --------------------------------------------------------------------- [ API ]


empty : AVLTree a
empty = Empty

partial
splitMax : AVLTree a -> (AVLTree a, a)
splitMax (Node _ e l Empty) = (l, e)
splitMax (Node _ e l r)     = let (r', e') = (splitMax r) in (balance e l r', e')

partial
merge : AVLTree a -> AVLTree a -> AVLTree a
merge l    Empty = l
merge Empty r    = r
merge l    r    = let (l', e) = (splitMax l) in balance e l' r


lookupUsing : Ord a => (a -> Ordering) -> AVLTree a -> Maybe a
lookupUsing _ Empty = Nothing
lookupUsing f (Node d x l r) =
  case f x of
    LT => lookupUsing f l
    GT => lookupUsing f r
    EQ => Just x

lookup : Ord a => a -> AVLTree a -> Maybe a
lookup v t = lookupUsing (compare v) t


insert : Ord a => a -> AVLTree a -> AVLTree a
insert e Empty          = mkNode e Empty Empty
insert x (Node d y l r) =
  case compare x y of
    LT => balance y (insert x l) r LT
    GT => balance y l (insert x r) GT
    EQ => Node d x l r


remove : Ord a => a -> AVLTree a -> AVLTree a
remove _ Empty          = Empty
remove x (Node d y l r) =
  case compare x y of
    LT => balance y (remove x l) r LT
    GT => balance y l (remove x r) GT
    EQ => merge l r


partial
updateUsing : Ord a => (a -> Ordering) -> (a -> a) -> AVLTree a -> AVLTree a
updateUsing _ _ Empty = Empty
updateUsing f t (Node d x l r) =
  case f x of
    LT => balance x (updateUsing f t l) r LT
    GT => balance x l (updateUsing f t r) GT
    EQ => Node d (t x) l r

partial
update : Ord a => a -> (a -> a) -> AVLTree a -> AVLTree a
update val f t = updateUsing (compare val) f t


partial
split : Ord a => a -> AVLTree a -> Maybe $ (AVLTree a, a)
split _ Empty          = Nothing
split x (Node d y l r) =
  case compare x y of
    LT => case split x l of
      Just (l', e) => Just (balance x l' r, e)
      Nothing      => Nothing
    GT => case split x r of
      Just (r', e) => Just (balance x l r', e)
      Nothing      => Nothing
    EQ => Just (merge l r, y)


length : AVLTree a -> Nat
length Empty = Z
length (Node _ _ l r) = 1 + length l + length r

-- -------------------------------------------------------------------- [ List ]
toList : AVLTree a -> List a
toList Empty          = Nil
toList (Node d e l r) = Tree.toList l ++ [e] ++ Tree.toList r


fromList : Ord a => List a -> AVLTree a
fromList Nil = Empty
fromList xs  = foldl (flip insert) Empty xs

-- --------------------------------------------------------------- [ Instances ]
instance Functor (AVLTree) where
  map f Empty          = Empty
  map f (Node d e l r) = Node d (f e) (map f l) (map f r)

instance Show a => Show (AVLTree a) where
  show x = show $ Tree.toList x

-- --------------------------------------------------------------------- [ EOF ]
