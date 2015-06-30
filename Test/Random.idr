module Test.Random

import Effects
import Effect.Random

genRndListU : (seed   : Integer)
          -> (bounds : (Integer, Integer))
          -> (length : Nat)
          -> List (Integer)
genRndListU s (l,u) n = runPure doBuild
  where
    genElem : (List Integer) -> Eff (Integer) [RND]
    genElem xs = do
      x <- rndInt l u
      if elem x xs
        then genElem xs
        else pure x

    genList : Nat -> Eff (List Integer) [RND]
    genList Z     = pure Nil
    genList (S c) = do
      xs <- genList c
      x <- genElem xs
      pure (x::xs)

    doBuild : Eff (List Integer) [RND]
    doBuild = do srand s; pure !(genList n)


genRndList : (seed   : Integer)
          -> (bounds : (Integer, Integer))
          -> (length : Nat)
          -> List (Integer)
genRndList s (l,u) n = runPure doBuild
  where
    genList : Nat -> Eff (List Integer) [RND]
    genList Z     = pure Nil
    genList (S c) = pure $ !(rndInt l u) :: !(genList c)

    doBuild : Eff (List Integer) [RND]
    doBuild = do srand s; pure !(genList n)


genRndKVList : (seed   : Integer)
            -> (bounds : (Integer, Integer))
            -> (length : Nat)
            -> List (Integer, Integer)
genRndKVList s (l,u) n = runPure doBuild
  where
    genList : Nat -> Eff (List (Integer,Integer)) [RND]
    genList Z     = pure Nil
    genList (S c) = pure $ (!(rndInt l u), !(rndInt l u) + (2*u)) :: !(genList c)

    doBuild : Eff (List (Integer,Integer)) [RND]
    doBuild = do srand s; pure !(genList n)

genRndKVListU : (seed   : Integer)
            -> (bounds : (Integer, Integer))
            -> (length : Nat)
            -> List (Integer, Integer)
genRndKVListU s (l,u) n = runPure doBuild
  where
    genElem : (List (Integer,Integer)) -> Eff (Integer) [RND]
    genElem xs = do
      x <- rndInt l u
      if isJust $ lookup x xs
        then genElem xs
        else pure x

    genList : Nat -> Eff (List (Integer,Integer)) [RND]
    genList Z     = pure Nil
    genList (S c) = do
      xs <- genList c
      x <- genElem xs
      pure $ ((x, x + (2*u)) :: xs)

    doBuild : Eff (List (Integer,Integer)) [RND]
    doBuild = do srand s; pure !(genList n)






-- --------------------------------------------------------------------- [ EOF ]
