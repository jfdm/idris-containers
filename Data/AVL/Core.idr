module Data.AVL.Core

import public Data.Tree

%default total
%access export

 -- ------------------------------------------------------------- [ Definitions ]
public export
data Balance : Nat -> Nat -> Type where
  LHeavy   : Balance (S n) n
  RHeavy   : Balance n     (S n)
  Balanced : Balance n     n

%name Balance b, bal

||| Indirection ensures that it reduces to at least S n' without
||| needing to case split on balance.
|||
||| Should make proofs easier.
public export
height : Balance n m -> Nat
height b = S (height' b)
  where
    height' : Balance n m -> Nat
    height' (LHeavy {n}) = S n
    height' (RHeavy {n}) = S n
    height' {n} (Balanced {n}) = n


||| Encoding of the AVL tree height invariants.
|||
||| @height The height of a Tree.
||| @tree   The tree whose height we are capturing.
public export
data AVLInvariant : (height : Nat)
                 -> (tree   : Tree k v)
                 -> Type
  where
    ||| A tree of height zero.
    AVLEmpty : AVLInvariant 0 Empty
    ||| A Balanced tree.
    |||
    ||| @left  The invariant of the left child.
    ||| @right The invariant of the right child.
    ||| @b     The encoding of the nodes' balance.
    AVLNode : (left  : AVLInvariant n l)
           -> (right :  AVLInvariant m r)
           -> (b : Balance n m)
           -> AVLInvariant (height b) (Node k v l r)

%name AVLInvariant inv

||| An AVL Tree.
|||
||| Modelled using subset to separate the invariants from the tree
||| implementation itself.
|||
||| @height  The height of the Tree.
||| @keyTy   The type associated with the keys.
||| @valueTy The type associated with the values.
public export
AVLTree : (height  : Nat)
       -> (keyTy   : Type)
       -> (valueTy : Type)
       -> Type
AVLTree n k v = Subset (Tree k v) (AVLInvariant n)

-- --------------------------------------------------------------- [ Rotations ]
public export
data InsertRes : Nat -> (k : Type) -> Type -> Type where
  Same : AVLTree n k v     -> InsertRes n k v
  Grew : AVLTree (S n) k v -> InsertRes n k v

%name InsertRes res, r

||| Process the result of an insertion of a new Key-Value pair into
||| the Tree, returning the new tree and proof of the new tree's
||| height.
|||
||| `InsertRes` is obtained from the result of running `Tree.insert`.
runInsertRes : InsertRes n k v -> (n : Nat ** AVLTree n k v)
runInsertRes (Same t) = (_ ** t)
runInsertRes (Grew t) = (_ ** t)

||| Perform a Left roation.
rotLeft : k
       -> v
       -> AVLTree n k v
       -> AVLTree (S (S n)) k v
       -> InsertRes (S (S n)) k v
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

||| Perform a Right rotation.
rotRight : k
        -> v
        -> AVLTree (S (S n)) k v
        -> AVLTree n k v
        -> InsertRes (S (S n)) k v
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


 --------------------------------------------------------------- [ Insertion ]

||| Perform an insertion into the tree returning the new tree wrapped
||| in a description describing the height change.
doInsert : (Ord k)
         => k
         -> v
         -> AVLTree n k v
         -> InsertRes n k v
doInsert newKey newVal (Element Empty AVLEmpty) = Grew (Element (Node newKey newVal Empty Empty)
                                                              (AVLNode AVLEmpty AVLEmpty Balanced))
doInsert newKey newVal (Element (Node key val l r) (AVLNode invl invr b)) with (compare newKey key)
  doInsert newKey newVal (Element (Node key val l r) (AVLNode invl invr b)) | EQ = Same (Element (Node newKey newVal l r) (AVLNode invl invr b))

  doInsert newKey newVal (Element (Node key val l r) (AVLNode invl invr b)) | LT with (assert_total $ doInsert newKey newVal (Element l invl))
    -- Totality checker not clever enough to see that this is smaller
    doInsert newKey newVal (Element (Node key val l r) (AVLNode invl invr b))        | LT | (Same (Element l' invl'))
                                                                                          = Same $ Element (Node key val l' r) (AVLNode invl' invr b)
    doInsert newKey newVal (Element (Node key val l r) (AVLNode invl invr LHeavy))   | LT | (Grew (Element l' invl'))
                                                                                          = rotRight key val (Element l' invl') (Element r invr)
    doInsert newKey newVal (Element (Node key val l r) (AVLNode invl invr Balanced)) | LT | (Grew (Element l' invl'))
                                                                                          = Grew $ Element (Node key val l' r) (AVLNode invl' invr LHeavy)
    doInsert newKey newVal (Element (Node key val l r) (AVLNode invl invr RHeavy))   | LT | (Grew (Element l' invl'))
                                                                                          = Same $ Element (Node key val l' r) (AVLNode invl' invr Balanced)

  doInsert newKey newVal (Element (Node key val l r) (AVLNode invl invr b)) | GT with (assert_total $ doInsert newKey newVal (Element r invr))
  -- Totality checker not clever enough to see that this is smaller
    doInsert newKey newVal (Element (Node key val l r) (AVLNode invl invr b))        | GT | (Same (Element r' invr'))
                                                                                          = Same $ Element (Node key val l r') (AVLNode invl invr' b)
    doInsert newKey newVal (Element (Node key val l r) (AVLNode invl invr LHeavy))   | GT | (Grew (Element r' invr'))
                                                                                          = Same $ Element (Node key val l r') (AVLNode invl invr' Balanced)
    doInsert newKey newVal (Element (Node key val l r) (AVLNode invl invr Balanced)) | GT | (Grew (Element r' invr'))
                                                                                          = Grew $ Element (Node key val l r') (AVLNode invl invr' RHeavy)
    doInsert newKey newVal (Element (Node key val l r) (AVLNode invl invr RHeavy))   | GT | (Grew (Element r' invr'))
                                                                                          = rotLeft key val (Element l invl) (Element r' invr')

||| Insert a key value pair into the tree, returning a the new tree
||| and possibly its new height.
insert : Ord k => k -> v -> AVLTree n k v -> (n : Nat ** AVLTree n k v)
insert k v t = runInsertRes (doInsert k v t)
