||| A version of `Dec` that returns a meaningful error message as well as proof of void.
|||
||| When dealing with decidable properties for type-level computations the existing `Dec` data type is useful.
||| However, when using decidable properties interactively one cannot easily tell why a property failed.
||| One can always encode failing cases within the property itself but that is not necessarily a advantageous.
|||
||| `DecInfo` provides a data structure to capture decidable properties together with an informative error message for when the property does not hold.
module Decidable.Error

%default total
%access public export


data DecInfo : (errType : Type) -> (prop : Type) -> Type where
   Yes : (prfWhy : prop) -> DecInfo errType prop
   No  : (msgWhyNot : errType) -> (prfWhyNot : prop -> Void) -> DecInfo errType prop

-- --------------------------------------------------------------------- [ EOF ]
