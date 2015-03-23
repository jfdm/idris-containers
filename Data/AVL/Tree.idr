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
module Data.Tree.AVL

-- @TODO Add dependent type and algebraic effect features to shore up
-- implementation.
--- @TODO Add complexity documentation.

%access private
--%default total

-- -------------------------------------------------------------- [ Definition ]
||| An AVL Tree.
|||
||| @a The element type.
public
data AVLTree : (a : Type) -> Type where
  Empty : AVLTree a
  Node : Nat -> a -> AVLTree a -> AVLTree a -> AVLTree a

height : AVLTree a -> Nat
height Empty           = Z
height (Node d a l r) = d

mkNode : a
       -> AVLTree a
       -> AVLTree a
       -> AVLTree a
mkNode e l r = Node (1+h) e l r
  where
    h : Nat
    h = max (height l) (height r)

public
avlIsEmpty : AVLTree e -> Bool
avlIsEmpty Empty = True
avlIsEmpty _    = False

-- ---------------------------------------------------------------- [ Rotation ]
bias : AVLTree a -> Nat
bias (Node _ _ l r)  = height l - height r
bias Empty           = 0

data ROTDIR = RotRL | RotRLB | RotLR | RotLRB | NOUT

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

rotr : AVLTree a -> AVLTree a
rotr Empty             = Empty
rotr (Node _ e l r)   with (l)
   | (Node _ e' l' r')  = mkNode e l (mkNode e' r r' )
   | Empty              = mkNode e l r

-- 'missing case' Empty might cause jip

rotl : AVLTree a -> AVLTree a
rotl Empty             = Empty
rotl (Node _ e l r) with (r)
  | (Node _ e' l' r') = mkNode e' (mkNode e l l') r'
  | Empty             = mkNode e l r

-- 'missing case 'Empty might cause jip

-- --------------------------------------------------------------- [ Balancing ]

balance : a -> AVLTree a -> AVLTree a -> AVLTree a
balance e l r = case rotDIR l r of
     RotRLB => rotr $ mkNode e (rotl l) r
     RotRL  => rotr $ mkNode e l r
     RotLRB => rotl $ mkNode e l $ rotr r
     RotLR  => rotl $ mkNode e l r
     NOUT   => mkNode e l r

-- --------------------------------------------------------------------- [ API ]
public
splitMax : AVLTree a -> (AVLTree a, a)
splitMax (Node _ e l Empty) = (l, e)
splitMax (Node _ e l r)    = let (r', e') = (splitMax r) in (balance e l r', e')

public
avlMerge : AVLTree a -> AVLTree a -> AVLTree a
avlMerge l    Empty = l
avlMerge Empty r    = r
avlMerge l    r    = let (l', e) = (splitMax l) in balance e l' r

public
avlLookup : Ord a => a -> AVLTree a -> Maybe a
avlLookup _ Empty          = Nothing
avlLookup x (Node d y l r) =
  case compare x y of
    LT => avlLookup x l
    GT => avlLookup x r
    EQ => Just y

public
avlInsert : Ord a => a -> AVLTree a -> AVLTree a
avlInsert e Empty          = mkNode e Empty Empty
avlInsert x (Node d y l r) =
  case compare x y of
    LT => balance y (avlInsert x l) r
    GT => balance y l (avlInsert x r)
    EQ => Node d x l r

public
avlRemove : Ord a => a -> AVLTree a -> AVLTree a
avlRemove _ Empty          = Empty
avlRemove x (Node d y l r) =
  case compare x y of
    LT => balance y (avlRemove x l) r
    GT => balance y l (avlRemove x r)
    EQ => avlMerge l r

public
avlUpdate : Ord a => a -> (a -> a) -> AVLTree a -> AVLTree a
avlUpdate _ _ Empty          = Empty
avlUpdate x f (Node d y l r) =
  case compare x y of
    LT => Node d x (avlUpdate x f l) r
    GT => Node d x l (avlUpdate x f r)
    EQ => Node d (f y) l r

public
avlSplit : Ord a => a -> AVLTree a -> Maybe $ (AVLTree a, a)
avlSplit _ Empty          = Nothing
avlSplit x (Node d y l r) =
  case compare x y of
    LT => case avlSplit x l of
      Just (l', e) => Just (balance x l' r, e)
      Nothing      => Nothing
    GT => case avlSplit x r of
      Just (r', e) => Just (balance x l r', e)
      Nothing      => Nothing
    EQ => Just (avlMerge l r, y)

public
avlIsElem : Ord a => a -> AVLTree a -> Bool
avlIsElem k t = case avlLookup k t of
   Nothing   => False
   otherwise => True

-- -------------------------------------------------------------------- [ List ]

public
avlToList : AVLTree a -> List a
avlToList Empty          = Nil
avlToList (Node d e l r) = e :: avlToList l ++ avlToList r

-- --------------------------------------------------------------- [ Instances ]
instance Functor (AVLTree) where
  map f Empty          = Empty
  map f (Node d e l r) = Node d (f e) (map f l) (map f r)

-- --------------------------------------------------------------------- [ EOF ]
