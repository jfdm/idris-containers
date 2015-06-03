module Data.Dependent.AVL.Tree

%default total

data Balance : Nat -> Nat -> Type where
  LeftLeaning  : Balance (S n) n
  RightLeaning : Balance n (S n)
  Balanced     : Balance n n

%name Balance b, bal

height : Balance n m -> Nat
height b = S (height' b)
        -- Indirection ensures that it reduces to at least S n' without needing to case split on balance
        -- Should make proofs easier
  where height' : Balance n m -> Nat
        height' (LeftLeaning {n}) = S n
        height' (RightLeaning {n}) = S n
        height' {n} (Balanced {n}) = n

data Tree' : Nat -> (k : Type) -> Ord k -> Type -> Type where
  Empty : Tree' 0 k o v
  Node : (l : Tree' n k o v) ->
         (key : k) -> (val : v) ->
         (r : Tree' m k o v) ->
         (b : Balance n m) -> Tree' (height b) k o v

%name Tree' t, tree

Tree : Nat -> (k : Type) -> {default %instance o : Ord k} -> Type -> Type
Tree n k {o = o} v = Tree' n k o v

lookup : (o : Ord k) => k -> Tree' n k o v -> Maybe v
lookup x Empty = Nothing
lookup x (Node l key val r b) =
  case compare x key of
    LT => lookup x l
    EQ => Just val
    GT => lookup x r

data InsertRes : Nat -> (k : Type) -> (o : Ord k) -> Type -> Type where
  Flat : Tree' n k o v -> InsertRes n k o v
  Taller : Tree' (S n) k o v -> InsertRes n k o v

%name InsertRes res, r

rotLeft : Tree' n k o v -> k -> v -> Tree' (S (S n)) k o v -> InsertRes (S (S n)) k o v
-- Impossible because Empty has depth 0 and we know the depth is at least 2 from the type
rotLeft l key val Empty impossible

rotLeft l key val (Node rl key' val' rr Balanced) =
  Taller $ Node (Node l key val rl RightLeaning) key' val' rr LeftLeaning

rotLeft l key val (Node (Node rll key'' val'' rlr LeftLeaning) key' val' rr LeftLeaning) =
  Flat $ Node rll key'' val'' (Node rlr key' val' rr RightLeaning) RightLeaning

rotLeft l key val (Node (Node rll key'' val'' rlr RightLeaning) key' val' rr LeftLeaning) =
  Flat $ Node (Node l key val rll LeftLeaning) key'' val'' (Node rlr key' val' rr Balanced) Balanced

rotLeft l key val (Node (Node rll key'' val'' rlr  Balanced) key' val' rr LeftLeaning) =
  Flat $ Node (Node l key val rll Balanced) key'' val'' (Node rlr key' val' rlr Balanced) Balanced

rotLeft l key val (Node rl key' val' rr RightLeaning) =
  Flat $ Node  (Node  l key val rl Balanced) key' val' rr Balanced



rotRight : Tree' (S (S n)) k o v -> k -> v -> Tree' n k o v -> InsertRes (S (S n)) k o v
rotRight Empty key val r impossible

rotRight (Node ll key val (Node lrl key' val' lrr RightLeaning) RightLeaning) key'' val'' r =
  Flat $ Node (Node ll key val lrl LeftLeaning) key' val' (Node lrr key'' val'' r Balanced) Balanced

rotRight (Node ll key val (Node lrl key' val' lrr LeftLeaning) RightLeaning) key'' val'' r =
  Flat $ Node (Node ll key val lrl Balanced) key' val' (Node lrr key'' val'' r RightLeaning) Balanced

rotRight (Node ll key' val' lr Balanced) key val r =
  Taller $ Node ll key' val' (Node lr key val r LeftLeaning) RightLeaning

rotRight (Node ll key' val' lr LeftLeaning) key val r =
  Flat $ Node ll key' val' (Node lr key val r Balanced) Balanced

rotRight (Node ll key' val' (Node lrl key'' val'' lrr Balanced) RightLeaning) key val r =
  Flat $ Node (Node ll key' val' lrl Balanced) key'' val'' (Node lrr key val r Balanced) Balanced


insert : (o : Ord k) => k -> v -> (t : Tree' n k o v) -> InsertRes n k o v
insert newKey newVal Empty = Taller (Node Empty newKey newVal Empty Balanced)
insert newKey newVal (Node l key val  r b) with (compare newKey key)
  insert newKey newVal (Node l key val r b) | EQ = Flat (Node l newKey newVal r b)
  insert newKey newVal (Node l key val r b) | LT with (insert newKey newVal l)
    insert newKey newVal (Node l key val r b)            | LT | (Flat l')   = Flat (Node l' key val r b)
    insert newKey newVal (Node l key val r LeftLeaning)  | LT | (Taller l') = rotRight l' key val r
    insert newKey newVal (Node l key val r Balanced)     | LT | (Taller l') = Taller (Node l' key val r LeftLeaning)
    insert newKey newVal (Node l key val r RightLeaning) | LT | (Taller l') = Flat (Node l' key val r Balanced)
  insert newKey newVal (Node l key val r b) | GT with (insert newKey newVal r)
    insert newKey newVal (Node l key val r b)            | GT | (Flat r')   = Flat (Node l key val r' b)
    insert newKey newVal (Node l key val r LeftLeaning)  | GT | (Taller r') = Flat (Node l key val r' Balanced)
    insert newKey newVal (Node l key val r Balanced)     | GT | (Taller r') = Taller (Node l key val r' RightLeaning)
    insert newKey newVal (Node l key val r RightLeaning) | GT | (Taller r') = rotLeft l key val r'


fromList : (o : Ord k) => List (k, v) -> (n : Nat ** Tree' n k o v)
fromList [] = (0 ** Empty)
fromList ((k, v) :: xs) with (insert k v (getProof (fromList xs)))
  fromList ((k, v) :: xs) | (Flat x) = (_ ** x)
  fromList ((k, v) :: xs) | (Taller x) = (_ ** x)


flatten : Tree' n k o v -> List (k, v)
flatten Empty = []
flatten (Node l key val r b) = flatten l ++ [(key, val)] ++ flatten r


tree1 : Tree 1 Int Int
tree1 = Node Empty 0 0 Empty (Balanced {n = 0})

test : InsertRes 3 Int %instance Int
test =
  let key : Int = 0 in let key' : Int = 0 in let key'' : Int = 0 in
  let val : Int = 0 in let val' : Int = 0 in let val'' : Int = 0 in
  let l : Tree 1 Int Int = tree1 in
  let rll : Tree 1 Int Int = tree1 in
  let rlr : Tree 0 Int Int = Empty in
  let rr : Tree 1 Int Int = tree1 in
  let rl : Tree 2 Int Int = Node rll key'' val'' rlr LeftLeaning in
  let r : Tree 3 Int Int = Node rl key' val' rr LeftLeaning in
  let res = rotLeft l 0 0 r in
  res

