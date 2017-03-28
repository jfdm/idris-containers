-- --------------------------------------------------------------- [ BitsUtils.idr ]
-- Module    : BitsUtils.idr
-- Copyright : (c) 2017 See CONTRIBUTORS.md
-- License   : see LICENSE
-- --------------------------------------------------------------------- [ EOH ]
||| Helper functions to work with `Data.Bits`.
module Data.Patricia.BitsUtils

import Data.Bits
import Data.Fin

%default total
%access public export

||| Checks if bit at index `i` is set to `0`.
isZeroBit : Fin n -> Bits n -> Bool
isZeroBit i b = not $ getBit i b

||| Sets the indicated bit to zero and all the lesser bits to one.
|||
||| @i Index of bit to set.
||| @b Target bits.
maskInsignificant : (i : Fin n) -> (b : Bits n) -> Bits n
maskInsignificant i b = and (b `or` minus m (cast 1)) (complement m) where
    m : Bits n
    m = intToBits $ pow 2 (finToNat i)  -- TODO: implement more efficiently?

||| Checks if bits key before _branching bit_ matches _prefix_ bits.
|||
||| @i Index of branching bit.
||| @p Prefix bits.
||| @k Key bits.
matchPrefix : (i : Fin n) -> (p : Bits n) -> (k : Bits n) -> Bool
matchPrefix i p k = maskInsignificant i k == p

{-
    // Fast Java implementation for 32bits

>>> public static int highestOneBit(int i) {
>>>     i |= (i >>  1);
>>>     i |= (i >>  2);
>>>     i |= (i >>  4);
>>>     i |= (i >>  8);
>>>     i |= (i >> 16);
>>>     return i - (i >>> 1);
>>> }
-}

-- TODO: make it true total
--   1. Ensure bits value under `b` is not zero
--   2. Ensure `natToFin` returns `Just` (use `fromInteger`?)
--   3. Ensure `shiftGo` returns not zero bits
-- TODO: make it fast
--   1. ¯\_(ツ)_/¯
||| Returns index of highest one bit set in `b`.
highestOneBit : Bits (S n) -> Fin (S n)  -- TODO: support Bits n -> Fin n ?
highestOneBit {n} b = bitsToFin $ shiftGo iterations b oneBit where
    iterations : Nat
    iterations = log2NZ (S n) SIsNotZ

    oneBit : Bits (S n)
    oneBit = cast 1

    shiftGo : Nat -> Bits (S n) -> Bits (S n) -> Bits (S n)
    shiftGo Z     i p = i `minus` (i `shiftRightLogical` oneBit)
    shiftGo (S k) i p = shiftGo k (i `or` (i `shiftRightArithmetic` p)) (p `shiftLeft` oneBit)

    bitsToFin : Bits (S n) -> Fin (S n)
    bitsToFin bits = fromMaybe FZ $ natToFin (log2NZ (toNat $ bitsToInt bits) believe_me) (S n)

branchingBit : Bits (S n) -> Bits (S n) -> Fin (S n)
branchingBit p0 p1 = highestOneBit $ xor p0 p1

-- --------------------------------------------------------------------- [ EOF ]
