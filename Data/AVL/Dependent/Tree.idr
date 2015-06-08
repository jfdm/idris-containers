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

data Tree : (k : Type) -> Ord k -> Type -> Type where
  Empty : Tree k o v
  Node : (key : k)
      -> (val : v)
      -> (l : Tree k o v)
      -> (r : Tree k o v)
      -> Tree k o v

%name Tree t, tree

data AVLInvariant : Nat -> (Tree k o v) -> Type where
  AVLEmpty : AVLInvariant 0 Empty
  AVLNode  : AVLInvariant n l -> AVLInvariant m r -> (b : Balance n m) -> AVLInvariant (height b) (Node k v l r)

%name AVLInvariant inv

AVLTree : (n : Nat) -> (k : Type) -> (o : Ord k) -> (v : Type) ->  Type
AVLTree n k o v = Subset (Tree k o v) (AVLInvariant n)

-- --------------------------------------------------------------- [ Rotations ]
data InsertRes : Nat -> (k : Type) -> (o : Ord k) -> Type -> Type where
  Same : AVLTree n k o v     -> InsertRes n k o v
  Grew : AVLTree (S n) k o v -> InsertRes n k o v

%name InsertRes res, r

runInsertRes : InsertRes n k o v -> (n : Nat ** AVLTree n k o v)
runInsertRes (Same t) = (_ ** t)
runInsertRes (Grew t) = (_ ** t)

rotLeft : k -> v -> AVLTree n k o v -> AVLTree (S (S n)) k o v -> InsertRes (S (S n)) k o v
-- Impossible because Empty has depth 0 and we know the depth is at least 2 from the type
rotLeft key val l (Element Empty AVLEmpty) impossible

rotLeft key val (Element l invl) (Element (Node key' val' rl rr) (AVLNode invrl invrr Balanced)) =
    Grew $ Element (Node key' val' (Node key val l rl) rr)
                        (AVLNode (AVLNode invl invrl RHeavy) invrr LHeavy)

rotLeft key val (Element l invl) (Element (Node key' val' (Node key'' val'' rll rlr) rr) (AVLNode (AVLNode invrll invrlr LHeavy) invrr LHeavy)) =
    Same $ Element (Node key'' val'' (Node key val l rll) (Node key' val' rlr rr)) -- Needs Checking
                        (AVLNode (AVLNode invl invrll Balanced) (AVLNode invrlr invrr RHeavy) Balanced)

rotLeft key val (Element l invl) (Element (Node key' val' (Node key'' val'' rll rlr) rr) (AVLNode (AVLNode invrll invrlr RHeavy) invrr LHeavy)) =
    Same $ Element (Node key'' val'' (Node key val l rll) (Node key' val' rlr rr))
                        (AVLNode (AVLNode invl invrll LHeavy) (AVLNode invrlr invrr Balanced) Balanced)

rotLeft key val (Element l invl) (Element (Node key' val' (Node key'' val'' rll rlr) rr) (AVLNode (AVLNode invrll invrlr Balanced) invrr LHeavy)) =
    Same $ Element (Node key'' val'' (Node key val l rll) (Node key' val' rlr rr))
                        (AVLNode (AVLNode invl invrll Balanced) (AVLNode invrlr invrr Balanced) Balanced) -- Needs Checking

rotLeft key val (Element l invl) (Element (Node key' val' rl rr) (AVLNode invrl invrr RHeavy)) =
    Same $ Element (Node key' val' (Node key val l rl) rr)
                        (AVLNode (AVLNode invl invrl Balanced) invrr Balanced)

rotRight : k -> v -> AVLTree (S (S n)) k o v -> AVLTree n k o v -> InsertRes (S (S n)) k o v
rotRight key val (Element Empty AVLEmpty) r impossible

rotRight key'' val'' (Element (Node key val ll (Node key' val' lrl lrr))
             (AVLNode invll (AVLNode invlrl invlrr RHeavy) RHeavy)) (Element r invr) =
  Same $ Element (Node key' val' (Node key val ll lrl) (Node key'' val'' lrr r))
                 (AVLNode (AVLNode invll invlrl LHeavy) (AVLNode invlrr invr Balanced) Balanced)

rotRight key'' val'' (Element (Node key val ll (Node key' val' lrl lrr))
             (AVLNode invll (AVLNode invlrl invlrr LHeavy) RHeavy)) (Element r invr) =
  Same $ Element (Node key' val' (Node key val ll lrl) (Node key'' val'' lrr r))
                 (AVLNode (AVLNode invll invlrl Balanced) (AVLNode invlrr invr RHeavy) Balanced)

rotRight key val (Element (Node key' val' ll lr) (AVLNode invll invlr Balanced)) (Element r invr) =
  Grew $ Element (Node key' val' ll (Node key val lr r))
                 (AVLNode invll (AVLNode invlr invr LHeavy) RHeavy)

rotRight key val (Element (Node key' val' ll lr) (AVLNode invll invlr LHeavy)) (Element r invr) =
  Same $ Element (Node key' val' ll (Node key val lr r))
                 (AVLNode invll (AVLNode invlr invr Balanced) Balanced)

rotRight key val (Element (Node key' val' ll (Node key'' val'' lrl lrr))
             (AVLNode invll (AVLNode invlrl invlrr Balanced) RHeavy)) (Element r invr) =
  Same $ Element (Node key'' val'' (Node key' val' ll lrl) (Node key val lrr r))
                 (AVLNode (AVLNode invll invlrl Balanced) (AVLNode invlrr invr Balanced) Balanced)

-- --------------------------------------------------------------- [ Insertion ]
insert : (o : Ord k) => k -> v -> (t : AVLTree n k o v) -> InsertRes n k o v
insert newKey newVal (Element Empty AVLEmpty) = Grew (Element (Node newKey newVal Empty Empty)
                                                              (AVLNode AVLEmpty AVLEmpty Balanced))
insert newKey newVal (Element (Node key val l r) (AVLNode invl invr b)) with (compare newKey key)
  insert newKey newVal (Element (Node key val l r) (AVLNode invl invr b)) | EQ = Same (Element (Node newKey newVal l r) (AVLNode invl invr b))

  insert newKey newVal (Element (Node key val l r) (AVLNode invl invr b)) | LT with (assert_total $ insert newKey newVal (Element l invl))
    -- Totality checker not clever enough to see that this is smaller
    insert newKey newVal (Element (Node key val l r) (AVLNode invl invr b))        | LT | (Same (Element l' invl'))
                                                                                          = Same $ Element (Node key val l' r) (AVLNode invl' invr b)
    insert newKey newVal (Element (Node key val l r) (AVLNode invl invr LHeavy))   | LT | (Grew (Element l' invl'))
                                                                                          = rotRight key val (Element l' invl') (Element r invr)
    insert newKey newVal (Element (Node key val l r) (AVLNode invl invr Balanced)) | LT | (Grew (Element l' invl'))
                                                                                          = Grew $ Element (Node key val l' r) (AVLNode invl' invr LHeavy)
    insert newKey newVal (Element (Node key val l r) (AVLNode invl invr RHeavy))   | LT | (Grew (Element l' invl'))
                                                                                          = Same $ Element (Node key val l' r) (AVLNode invl' invr Balanced)

  insert newKey newVal (Element (Node key val l r) (AVLNode invl invr b)) | GT with (assert_total $ insert newKey newVal (Element r invr))
  -- Totality checker not clever enough to see that this is smaller
    insert newKey newVal (Element (Node key val l r) (AVLNode invl invr b))        | GT | (Same (Element r' invr'))
                                                                                          = Same $ Element (Node key val l r') (AVLNode invl invr' b)
    insert newKey newVal (Element (Node key val l r) (AVLNode invl invr LHeavy))   | GT | (Grew (Element r' invr'))
                                                                                          = Same $ Element (Node key val l r') (AVLNode invl invr' Balanced)
    insert newKey newVal (Element (Node key val l r) (AVLNode invl invr Balanced)) | GT | (Grew (Element r' invr'))
                                                                                          = Grew $ Element (Node key val l r') (AVLNode invl invr' RHeavy)
    insert newKey newVal (Element (Node key val l r) (AVLNode invl invr RHeavy))   | GT | (Grew (Element r' invr'))
                                                                                          = rotLeft key val (Element l invl) (Element r' invr')

lookup : (o : Ord k) => k -> AVLTree h k o v -> Maybe v
lookup key (Element t _) = lookup' key t
  where lookup' : (o : Ord k) => k -> Tree k o v -> Maybe v
        lookup' key Empty = Nothing
        lookup' key (Node key' value' l r) with (compare key key')
          lookup' key (Node key' value' l r) | LT = lookup' key l
          lookup' key (Node key' value' l r) | EQ = Just value'
          lookup' key (Node key' value' l r) | GT = lookup' key r

update : (o : Ord k) => k -> (v -> v) -> AVLTree h k o v -> AVLTree h k o v
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

foldr : (step : k -> v -> p -> p) -> (init : p) -> AVLTree n k o v -> p
foldr step init (Element t _) = foldr' step init t
  where foldr' : (k -> v -> p -> p) -> p -> Tree k o v -> p
        foldr' step' init' Empty = init'
        foldr' step' init' (Node key val l r) = foldr' step' (step' key val (foldr' step' init' r)) l

fromList : (o : Ord k) => List (k, v) -> (n : Nat ** AVLTree n k o v)
fromList [] = (0 ** Element Empty AVLEmpty)
fromList ((k, v) :: xs) with (insert k v (getProof (fromList xs)))
  fromList ((k, v) :: xs) | (Same x) = (_ ** x)
  fromList ((k, v) :: xs) | (Grew x) = (_ ** x)

toList : AVLTree n k o v -> List (k, v)
toList = foldr (\k,v,xs => (k, v) :: xs) []

size : AVLTree h k o v -> Nat
size = foldr (\_,_=> S) 0

keys : AVLTree h k o v -> List k
keys = map fst . toList

values : AVLTree h k o v -> List v
values = map snd . toList

all : (pred : k -> v -> Bool) ->  AVLTree h k o v -> Bool
all pred = foldr (\k,v,pred' => pred' && pred k v) True

any : (pred : k -> v -> Bool) ->  AVLTree h k o v -> Bool
any pred = foldr (\k,v,pred' => pred' || pred k v) False

hasKey : (o : Ord k) => k -> AVLTree h k o v -> Bool
hasKey key = any (\key',value' => key == key')

hasValue : (Eq v) => v -> AVLTree h k o v -> Bool
hasValue value = any (\key',value' => value == value')

findKey : (pred : v -> Bool) -> AVLTree h k o v -> Maybe k
findKey pred = foldr (\k,v,p => if pred v then Just k else p) Nothing

findKeyOf : (Eq v) => v -> AVLTree h k o v -> Maybe k
findKeyOf value = findKey (== value)

-- ----------------------------------------------------------------- [ Classes ]
eqTree : (Eq k, Eq v) => Tree k o v -> Tree k o v -> Bool
eqTree Empty              Empty              = True
eqTree (Node xk xv xl xr) (Node yk yv yl yr) =
  xk == yk  &&
  xv == yv  &&
  eqTree xl yl &&
  eqTree xr yr
eqTree _ _                                   = False

instance (Eq k, Eq v) => Eq (Tree k o v) where
  (==) x y = eqTree x y

instance (Eq k, Eq v) => Eq (AVLTree h k o v) where
  (==) (Element t _) (Element t' _) = t == t'

instance (Show k, Show v) => Show (Tree k o v) where
  show Empty              = ""
  show (Node k v l r)     = unwords ["{", show l, "(", show k, ":", show v, "),", show r, "}"]

instance (Show k, Show v) => Show (AVLTree h k o v) where
  show (Element t _) = show t

-- --------------------------------------------------------------------- [ EOF ]
