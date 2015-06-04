||| A Dependently Typed Implementation of an AVL Tree optimised for
||| Dictionaries.
|||
||| This code is dervied from an original design by David
||| Christiansen.
|||
||| *Note* When using this Data Structure, the design is such that the
||| tree does not factor in unbalanced trees and so removal of items is not permited.
module Data.AVL.Dependent.Tree

%default total

-- ------------------------------------------------------------- [ Definitions ]
data Balance : Nat -> Nat -> Type where
  LHeavy   : Balance (S n) n
  RHeavy   : Balance n     (S n)
  Balanced : Balance n     n

%name Balance b, bal

-- Indirection ensures that it reduces to at least S n' without needing to case split on balance
-- Should make proofs easier
height : Balance n m -> Nat
height b = S (height' b)
  where
    height' : Balance n m -> Nat
    height' (LHeavy {n}) = S n
    height' (RHeavy {n}) = S n
    height' {n} (Balanced {n}) = n

data Tree : Nat -> (k : Type) -> Ord k -> Type -> Type where
  Empty : Tree 0 k o v
  Node : (key : k)
      -> (val : v)
      -> (l : Tree n k o v)
      -> (r : Tree m k o v)
      -> (b : Balance n m)
      -> Tree (height b) k o v

%name Tree t, tree

-- --------------------------------------------------------------- [ Rotations ]
data InsertRes : Nat -> (k : Type) -> (o : Ord k) -> Type -> Type where
  Same : Tree n k o v     -> InsertRes n k o v
  Grew : Tree (S n) k o v -> InsertRes n k o v

%name InsertRes res, r

rotLeft : k -> v -> Tree n k o v -> Tree (S (S n)) k o v -> InsertRes (S (S n)) k o v
-- Impossible because Empty has depth 0 and we know the depth is at least 2 from the type
rotLeft key val l Empty                           impossible

rotLeft key val l (Node key' val' rl rr Balanced) =
    Grew $ Node key' val' (Node key val l rl RHeavy) rr LHeavy

rotLeft key val l (Node key' val' (Node key'' val'' rll rlr LHeavy) rr LHeavy) =
    Same $ Node key'' val'' rll (Node key' val' rlr rr RHeavy) RHeavy

rotLeft key val l (Node key' val' (Node key'' val'' rll rlr RHeavy) rr LHeavy) =
    Same $ Node key'' val'' (Node key val l rll LHeavy) (Node key' val' rlr rr Balanced) Balanced

rotLeft key val l (Node key' val' (Node key'' val'' rll rlr  Balanced) rr LHeavy) =
    Same $ Node key'' val'' (Node key val l rll Balanced) (Node key' val' rlr rlr Balanced) Balanced

rotLeft key val l (Node key' val' rl rr RHeavy) =
    Same $ Node key' val' (Node key val l rl Balanced) rr Balanced



rotRight : k -> v -> Tree (S (S n)) k o v -> Tree n k o v -> InsertRes (S (S n)) k o v
rotRight key val Empty r impossible

rotRight key'' val'' (Node key val ll (Node key' val' lrl lrr RHeavy) RHeavy) r =
  Same $ Node key' val' (Node key val ll lrl LHeavy) (Node key'' val'' lrr r Balanced) Balanced

rotRight key'' val'' (Node key val ll (Node key' val' lrl lrr LHeavy) RHeavy) r =
  Same $ Node key' val' (Node key val ll lrl Balanced) (Node key'' val'' lrr r RHeavy) Balanced

rotRight key val (Node key' val' ll lr Balanced) r =
  Grew $ Node key' val' ll (Node key val lr r LHeavy) RHeavy

rotRight key val (Node key' val' ll lr LHeavy) r =
  Same $ Node key' val' ll (Node key val lr r Balanced) Balanced

rotRight key val (Node key' val' ll (Node key'' val'' lrl lrr Balanced) RHeavy) r =
  Same $ Node key'' val'' (Node key' val' ll lrl Balanced) (Node key val lrr r Balanced) Balanced

-- --------------------------------------------------------------- [ Insertion ]
insert : (o : Ord k) => k -> v -> (t : Tree n k o v) -> InsertRes n k o v
insert newKey newVal Empty = Grew (Node newKey newVal Empty Empty Balanced)
insert newKey newVal (Node key val l r b) with (compare newKey key)
  insert newKey newVal (Node key val l r b) | EQ = Same (Node newKey newVal l r b)

  insert newKey newVal (Node key val l r b) | LT with (insert newKey newVal l)
    insert newKey newVal (Node key val l r b)        | LT | (Same l') = Same (Node key val l' r b)
    insert newKey newVal (Node key val l r LHeavy)   | LT | (Grew l') = rotRight key val l' r
    insert newKey newVal (Node key val l r Balanced) | LT | (Grew l') = Grew (Node key val l' r LHeavy)
    insert newKey newVal (Node key val l r RHeavy)   | LT | (Grew l') = Same (Node key val l' r Balanced)

  insert newKey newVal (Node key val l r b) | GT with (insert newKey newVal r)
    insert newKey newVal (Node key val l r b)        | GT | (Same r') = Same (Node key val l r' b)
    insert newKey newVal (Node key val l r LHeavy)   | GT | (Grew r') = Same (Node key val l r' Balanced)
    insert newKey newVal (Node key val l r Balanced) | GT | (Grew r') = Grew (Node key val l r' RHeavy)
    insert newKey newVal (Node key val l r RHeavy)   | GT | (Grew r') = rotLeft key val l r'

-- ------------------------------------------------------------------ [ Update ]

||| Update value in the dictionary in place selecting key using a
||| custom comparison function.
updateValueBy : (o : Ord k) => (k -> Ordering)
                            -> (v -> v)
                            -> Tree h k o v
                            -> InsertRes h k o v
updateValueBy cmp ufunc Empty = Same Empty
updateValueBy cmp ufunc (Node key val l r b) with (cmp key)
  updateValueBy cmp ufunc (Node key val l r b) | EQ = Same (Node key (ufunc val) l r b)

  updateValueBy cmp ufunc (Node key val l r b) | LT with (updateValueBy cmp ufunc l)
    updateValueBy cmp ufunc (Node key val l r b)        | LT | (Same l') = Same (Node key val l' r b)
    updateValueBy cmp ufunc (Node key val l r LHeavy)   | LT | (Grew l') = rotRight key val l' r
    updateValueBy cmp ufunc (Node key val l r Balanced) | LT | (Grew l') = Grew (Node key val l' r LHeavy)
    updateValueBy cmp ufunc (Node key val l r RHeavy)   | LT | (Grew l') = Same (Node key val l' r Balanced)

  updateValueBy cmp ufunc (Node key val l r b) | GT with (updateValueBy cmp ufunc r)
    updateValueBy cmp ufunc (Node key val l r b)        | GT | (Same r') = Same (Node key val l r' b)
    updateValueBy cmp ufunc (Node key val l r LHeavy)   | GT | (Grew r') = Same (Node key val l r' Balanced)
    updateValueBy cmp ufunc (Node key val l r Balanced) | GT | (Grew r') = Grew (Node key val l r' RHeavy)
    updateValueBy cmp ufunc (Node key val l r RHeavy)   | GT | (Grew r') = rotLeft key val l r'


fromList : (o : Ord k) => List (k, v) -> (n : Nat ** Tree n k o v)
fromList [] = (0 ** Empty)
fromList ((k, v) :: xs) with (insert k v (getProof (fromList xs)))
  fromList ((k, v) :: xs) | (Same x) = (_ ** x)
  fromList ((k, v) :: xs) | (Grew x) = (_ ** x)

toList : Tree n k o v -> List (k, v)
toList Empty = []
toList (Node key val l r b) = toList l ++ [(key, val)] ++ toList r


lookupUsing : Ord k => (k -> Ordering) -> Tree h k o v -> Maybe v
lookupUsing _ Empty        	   = Nothing
lookupUsing f (Node k v l r b) =
  case f k of
    LT => lookupUsing f l
    GT => lookupUsing f r
    EQ => Just v

lookup : Ord k => k -> Tree h k o v -> Maybe v
lookup k d = lookupUsing (compare k) d

keys : Ord k => Tree h k o v -> List k
keys Empty = Nil
keys (Node k _ l r b) = keys l ++ [k] ++ keys r

values : Ord k => Tree h k o v -> List v
values Empty = Nil
values (Node _ v l r b) = values l ++ [v] ++ values r

length : Ord k => Tree h k o v -> Nat
length Empty = Z
length (Node _ _ l r b) = 1 + length l + length r

hasKeyUsing : (Ord k) => (k -> Ordering) -> Tree h k o v -> Bool
hasKeyUsing f Empty = False
hasKeyUsing f (Node k v l r b) =
  case f k of
    EQ => True
    LT => (hasKeyUsing f l)
    GT => (hasKeyUsing f r)

hasKey : (Ord k) => k -> Tree h k o v -> Bool
hasKey k d = hasKeyUsing (compare k) d

hasValueUsing : Ord k => (v -> Bool) -> Tree h k o v -> Bool
hasValueUsing f Empty = False
hasValueUsing f (Node k v l r b) =
  f v || (hasValueUsing f l) || (hasValueUsing f r)

hasValue : (Ord k, Eq v) => v -> Tree h k o v -> Bool
hasValue v d = hasValueUsing (\x => v == x) d

getKeyUsing : Ord k => (v -> Bool) -> Tree h k o v -> Maybe k
getKeyUsing f Empty = Nothing
getKeyUsing f d     =
    foldr (\acc,res => isRes f acc res) Nothing $ Tree.toList d
  where
    isRes : (v -> Bool) -> (k,v) -> Maybe k -> Maybe k
    isRes f (k,v) r = case f v of
                         True  => Just k
                         False => r

getKey : (Ord k, Eq v) => v -> Tree h k o v -> Maybe k
getKey v d = getKeyUsing (\x => x==v) d

-- --------------------------------------------------------------------- [ EOF ]
