module Decidable.Equality.Indexed

%default total
%access public export

interface DecEq iTy
       => DecEqIdx (iTy : Type)
                   (eTy : iTy -> Type) | eTy
  where
     decEq : {i,j : iTy}
          -> (x : eTy i)
          -> (y : eTy j)
          -> (prf : i = j)
          -> Dec (x = y)
