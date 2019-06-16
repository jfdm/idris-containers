-- ---------------------------------------------------------- [ Predicates.idr ]
-- Module    : Predicates.idr
-- Copyright : (c) Jan de Muijnck-Hughes
-- License   : see LICENSE
-- --------------------------------------------------------------------- [ EOH ]

||| More Quantifiers for Lists, but keeping them out of the prelude so
||| need a new module name.
module Data.List.Predicates

import public Data.List
import public Data.List.Predicates.Unique
import public Data.List.Predicates.Interleaving
import public Data.List.Predicates.Pairs
import public Data.List.Predicates.Thinning

%default total
%access public export




-- --------------------------------------------------------------------- [ EOF ]
