-- -------------------------------------------------------------- [ Values.idr ]
-- Module    : Values.idr
-- Copyright : (c) Jan de Muijnck-Hughes
-- License   : see LICENSE
-- --------------------------------------------------------------------- [ EOH ]
module Test.Random.Values

import Effects
import Effect.Random

%access export

-- --------------------------------------------------------- [ List Generators ]

genRndListE : (seed      : Integer)
           -> (len       : Nat)
           -> (generator : Eff a [RND])
           -> Eff (List a) [RND]
genRndListE s l f = do srand s; pure !(doGen l f)
  where
    doGen : (len : Nat)
         -> (generator : Eff a [RND])
         -> Eff (List a) [RND]
    doGen Z     f = pure List.Nil
    doGen (S n) f = pure $ (!f :: !(doGen n f))

genRndListUE : Eq a =>
               (seed      : Integer)
            -> (len       : Nat)
            -> (generator : Eff a [RND])
            -> Eff (List a) [RND]
genRndListUE s l f = do srand s; pure !(doGen l f)
  where
    genElem : Eq a => Eff a [RND] -> List a -> Eff a [RND]
    genElem f xs = do
      x <- f
      if elem x xs
        then genElem f xs
        else pure x

    doGen : Eq a => Nat -> Eff a [RND] -> Eff (List a) [RND]
    doGen Z     f = pure Nil
    doGen (S n) f = do
      xs <- doGen n f
      x  <- genElem f xs
      pure (x::xs)

genKVPair : (genA : Eff a [RND])
         -> (genB : Eff b [RND])
         -> Eff (Pair a b) [RND]
genKVPair f g = pure (!f, !g)


genRndListKVE : (seed : Integer)
             -> (len  : Nat)
             -> (genA : Eff a [RND])
             -> (genB : Eff b [RND])
             -> Eff (List (Pair a b)) [RND]
genRndListKVE s l f g = genRndListE s l (genKVPair f g)


genRndListKVUE : (Eq a, Eq b) =>
                 (seed : Integer)
              -> (len  : Nat)
              -> (genA : Eff a [RND])
              -> (genB : Eff b [RND])
              -> Eff (List (Pair a b)) [RND]
genRndListKVUE s l f g = do srand s; pure !(doGen l (genKVPair f g))
  where
    genElem : (Eq a, Eq b) => Eff (Pair a b) [RND] -> List (Pair a b) -> Eff (Pair a b) [RND]
    genElem f xs = do
      x <- f
      if elem x xs
        then genElem f xs
        else if isJust $ lookup (fst x) xs
          then genElem f xs
          else pure x

    doGen : (Eq a, Eq b) => Nat -> Eff (Pair a b) [RND] -> Eff (List (Pair a b)) [RND]
    doGen Z     f = pure Nil
    doGen (S n) f = do
      xs <- doGen n f
      x  <- genElem f xs
      pure (x::xs)


-- -------------------------------------------------------- [ Random Int Lists ]


rndListIntE : (seed   : Integer)
           -> (bounds : Pair Integer Integer)
           -> (length : Nat)
           -> Eff (List Integer) [RND]
rndListIntE s (l,u) n = genRndListE s n (rndInt l u)

rndListInt : (seed   : Integer)
          -> (bounds : Pair Integer Integer)
          -> (length : Nat)
          -> List (Integer)
rndListInt s bs n = runPure $ rndListIntE s bs n

-- ------------------------------------------------- [ Random Unique Int Lists ]

rndListIntUE : (seed   : Integer)
            -> (bounds : Pair Integer Integer)
            -> (len    : Nat)
            -> Eff (List Integer) [RND]
rndListIntUE s (l,u) n = genRndListUE s n (rndInt l u)

rndListIntU : (seed   : Integer)
           -> (bounds : Pair Integer Integer)
           -> (len    : Nat)
           -> List Integer
rndListIntU s bs n = runPure $ rndListIntUE s bs n

-- ------------------------------------------------- [ Random Int KV Pair List ]

genY : Integer -> Integer -> Eff Integer [RND]
genY l u = do
  x <- rndInt l u
  pure (x + 2*u)

rndListIntKVE : (seed   : Integer)
             -> (bounds : Pair Integer Integer)
             -> (len    : Nat)
             -> Eff (List (Pair Integer Integer)) [RND]
rndListIntKVE s (l,u) n = genRndListKVE s n (rndInt l u) (genY l u)

rndListIntKV : (seed   : Integer)
            -> (bounds : Pair Integer Integer)
            -> (len    : Nat)
            -> List (Pair Integer Integer)
rndListIntKV s bs n = runPure $ rndListIntKVE s bs n

rndListIntKVUE : (seed   : Integer)
              -> (bounds : Pair Integer Integer)
              -> (len    : Nat)
              -> Eff (List (Pair Integer Integer)) [RND]
rndListIntKVUE s (l,u) n = genRndListKVUE s n (rndInt l u) (genY l u)

rndListIntKVU : (seed   : Integer)
             -> (bounds : Pair Integer Integer)
             -> (len    : Nat)
             -> List (Pair Integer Integer)
rndListIntKVU s bs n = runPure $ rndListIntKVUE s bs n


-- --------------------------------------------------------------------- [ EOF ]
