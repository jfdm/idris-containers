module Data.List.LeftPad

import Data.List
import Data.List.Predicates.Interleaving

%default total
%access public export

data Padding : (s : List Char) -> (target : Nat) -> Type where
  Pad : (pad : Nat) -> Padding s (length s + pad)
  Nop : Padding (ys ++ x :: xs) (length ys)

padding : (s : List Char) -> (target : Nat) -> Padding s target
padding       []     t  = Pad t
padding (x :: xs)    Z  = Nop {ys = []}
padding (x :: xs) (S t) with (padding xs t)
  padding (x :: xs) (S (plus (length xs) p))   | Pad p = Pad p
  padding (y :: ys ++ z :: zs) (S (length ys)) | Nop   = Nop {ys=y::ys}

pad : (s : List Char) -> (c : Char) -> (target : Nat) -> List Char
pad s c target with (padding s target)
  pad s c (length s + pad)          | Pad pad  = replicate pad c ++ s
  pad (ys ++ x :: xs) c (length ys) | Nop {ys} = ys ++ x :: xs


namespace MorePad
  Pad : (s : List Char) -> (c : Char) -> (target : Nat) -> Type
  Pad s c target with (padding s target)
    Pad s c ((length s) + pad) | (Pad pad) = let ps = replicate pad c in Interleaving ps s (ps ++ s)

    Pad (ys ++ (x :: xs)) c (length ys) | Nop = Interleaving Nil (ys ++ (x :: xs)) (ys ++ (x :: xs))

  noPad : (s : List Char) -> Interleaving Nil s s
  noPad [] = Empty
  noPad (x :: xs) = RightAdd x (noPad xs)

  addPadd : (pad : List Char) -> (s : List Char) -> Interleaving pad s (pad ++ s)
  addPadd [] s = noPad s
  addPadd (x :: xs) s = LeftAdd x (addPadd xs s)

  pad : (s : List Char) -> (c : Char) -> (target : Nat) -> Pad s c target
  pad s c target with (padding s target)
    pad s c ((length s) + pad) | (Pad pad) = let ps = replicate pad c in addPadd ps s
    pad (ys ++ (x :: xs)) c (length ys) | Nop = noPad (ys ++ (x::xs))
