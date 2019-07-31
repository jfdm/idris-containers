-- ---------------------------------------------------------------- [ Tree.idr ]
-- Module    : Tree.idr
-- Copyright : (c) 2015,2016 See CONTRIBUTORS.md
-- License   : see LICENSE
-- --------------------------------------------------------------------- [ EOH ]
||| A Dependently Typed Implementation of an AVL Tree optimised for
||| Dictionaries.
|||
||| This code is dervied from an original design by David
||| Christiansen.
|||
||| *Note* When using this Data Structure, the design is such that the
||| tree does not factor in unbalanced trees and so removal of items
||| is not permited.
module Data.AVL

import public Data.Tree
import public Data.AVL.Core
import public Data.AVL.Core.API
import public Data.AVL.Core.Quantifiers
