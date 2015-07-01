-- ----------------------------------------------------------------- [ Eff.idr ]
-- Module    : Eff.idr
-- Copyright : (c) Jan de Muijnck-Hughes
-- License   : see LICENSE
-- --------------------------------------------------------------------- [ EOH ]

module Data.Sigma.DList.Eff

import Effects

import Data.Sigma.DList

mapDListE : ({a : aTy} -> elemTy a -> {xs} EffM m b)
         -> DList aTy elemTy as -> {xs} EffM m (List b)
mapDListE f Nil       = pure List.Nil
mapDListE f (x :: xs) = with List [| f x :: mapDListE f xs |]


foldrE : ({a : aTy} -> elemTy a -> p -> {xs} EffM m p)
     -> p
     -> DList aTy elemTy as
     -> {xs} EffM m p
foldrE f init Nil     = pure init
foldrE f init (x::xs) = do
    ires <- foldrE f init xs
    pure $ !(f x ires)

foldlE : ({a : aTy} -> p -> elemTy a -> {xs} EffM m p)
      -> p
      -> DList aTy elemTy as
      -> {xs} EffM m p
foldlE f init Nil     = pure init
foldlE f init (x::xs) = do
    ires <- f init x
    pure $ !(foldlE f ires xs)

-- --------------------------------------------------------------------- [ EOF ]
