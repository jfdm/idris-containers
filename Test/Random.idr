module Test.Random

import Effects
import Effect.Random


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


-- --------------------------------------------------------------------- [ EOF ]
