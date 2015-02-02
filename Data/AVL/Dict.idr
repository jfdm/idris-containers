||| Implementation of an  Binary Search Tree optimised for Dictionaries.
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
module Data.AVL.Dict

-- @TODO Add dependent type and algebraic effect features to shore up
-- implementation.
-- @TODO Add complexity documentation.

%access public

-- -------------------------------------------------------------- [ Definition ]
||| An  Dict design for implementing a finite map.
|||
||| @k The type of the key.
||| @v The type of the value.
data Dict : (k : Type) -> (v : Type) -> Type where
  Empty : Dict k v
  Node : Nat -> (k,v) -> Dict k v -> Dict k v -> Dict k v

private
height : Ord k => Dict k v -> Nat
height Empty             = Z
height (Node d (k,v) l r) = d

private
mkNode : Ord k => k -> v
       -> Dict k v
       -> Dict k v
       -> Dict k v
mkNode k v l r = Node (1+h) (k,v) l r
  where
    h : Nat
    h = max (height l) (height r)

-- ---------------------------------------------------------------- [ Rotation ]
private
bias : Ord k => Dict k v -> Nat
bias (Node _ _ l r) = height l - height r
bias Empty             = 0

private
data ROTDIR = RotRL | RotRLB | RotLR | RotLRB | NOUT

private
rotDIR : Ord k => Dict k v -> Dict k v -> ROTDIR
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
rotr : Ord k => Dict k v -> Dict k v
rotr Empty             = Empty
rotr (Node _ (k,v) l r) with (l)
  | (Node _ (k',v') l' r') = mkNode k v l (mkNode k' v' r r' )
-- 'missing case' Empty might cause jip

private
rotl : Ord k => Dict k v -> Dict k v
rotl Empty             = Empty
rotl (Node _ (k,v) l r) with (r)
  | (Node _ (k',v') l' r') = mkNode k' v' (mkNode k v l l') r'
-- 'missing case 'Empty might cause jip

-- --------------------------------------------------------------- [ Balancing ]
private
balance : Ord k => k -> v -> Dict k v -> Dict k v -> Dict k v
balance k v l r = case rotDIR l r of
     RotRLB => rotr $ mkNode k v (rotl l) r
     RotRL  => rotr $ mkNode k v l r
     RotLRB => rotl $ mkNode k v l $ rotr r
     RotLR  => rotl $ mkNode k v l r
     NOUT   => mkNode k v l r

-- --------------------------------------------------------------------- [ API ]

empty : Dict k v
empty = Empty

isEmpty : Dict k v -> Bool
isEmpty Empty = True
isEmpty _    = False

||| Note this is not the classical split.
splitMax : Ord k => Dict k v -> (Dict k v, (k,v))
splitMax (Node _ (k,v) l Empty) = (l, (k,v))
splitMax (Node _ (k,v) l r)    = let (r', (k',v')) = (splitMax r) in (balance k v l r', (k',v'))


merge : Ord k => Dict k v -> Dict k v -> Dict k v
merge l    Empty = l
merge Empty r    = r
merge l    r     = let (l', (k,v)) = (splitMax l) in balance k v l' r


lookup : Ord k => k -> Dict k v -> Maybe v
lookup _ Empty              = Nothing
lookup x (Node d (y,v) l r) =
    case compare x y of
      LT => lookup x l
      GT => lookup x r
      EQ => Just v

isKey : Ord k => k -> Dict k v -> Bool
isKey k d = isJust $ lookup k d

insert : Ord k => k -> v -> Dict k v -> Dict k v
insert k v Empty              = mkNode k v Empty Empty
insert x a (Node d (y,b) l r) =
     case compare x y of
     LT => balance y b (insert x a l) r
     GT => balance y b l (insert x a r)
     EQ => Node d (x,a) l r

remove : Ord k => k -> Dict k v -> Dict k v
remove _ Empty              = Empty
remove x (Node d (y,v) l r) =
  case compare x y of
    LT => balance y v (remove x l) r
    GT => balance y v l (remove x r)
    EQ => merge l r

update : Ord k => k -> (v -> v) -> Dict k v -> Dict k v
update _ _ Empty              = Empty
update x f (Node d (y,v) l r) =
  case compare x y of
    LT => Node d (y,v) (update x f l) r
    GT => Node d (y,v) l (update x f r)
    EQ => Node d (y,(f v)) l r

||| Note this is not the classical split
split : Ord k => k -> Dict k v -> Maybe $ (Dict k v, (k,v))
split _ Empty = Nothing
split x (Node d (y,v) l r) =
  case compare x y of
    LT => case split x l of
      Just (l', (k',v')) => Just (balance x v l' r, (k',v'))
      Nothing            => Nothing
    GT => case split x r of
      Just (r', (k',v')) => Just (balance x v l r', (k',v'))
      Nothing            => Nothing
    EQ => Just (merge l r, (y,v))


keys : Dict k v -> List k
keys Empty              = Nil
keys (Node _ (k,v) l r) = keys l ++ [k] ++ keys r

values : Dict k v -> List v
values Empty              = Nil
values (Node _ (k,v) l r) = values l ++ [v] ++ values r

length : Dict k v -> Nat
length Empty = Z
length (Node _ _ l r) = 1 + length l + length r

-- -------------------------------------------------------------------- [ List ]

toList : Dict k v -> List (k,v)
toList Empty              = Nil
toList (Node d (k,v) l r) = (k,v) :: toList l ++ toList r

fromList : Ord k => List (k,v) -> Dict k v
fromList xs = foldl (\d, (k,v)=> insert k v d) Empty xs


-- ---------------------------------------------------------------- [ Instance ]
instance (Show k, Show v) => Show (Dict k v) where
  show Empty              = ""
  show (Node d (k,v) l r) = unwords ["{", show l, "(", show k, ":", show v, "),", show r, "}"]

instance Functor (Dict k) where
  map f Empty = Empty
  map f (Node d (k,v) l r) = Node d (k, f v) (map f l) (map f r)

-- --------------------------------------------------------------------- [ EOF ]
