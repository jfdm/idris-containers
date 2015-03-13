||| A `list` construct to create lists of dependent types.
module SigmaList



using (aTy : Type, elemTy : (aTy -> Type), x : aTy)

  ||| A list construct for dependent types.
  |||
  ||| @aTy    The type of the value contained within the list element type.
  ||| @elemTy The type of the elements within the list
  ||| @as     The List used to contain the different values within the type.
  data SigmaList : (aTy : Type)
            -> (elemTy : aTy -> Type)
            -> (as : List aTy)
            -> Type where
    ||| Create an empty List
    Nil  : SigmaList aTy elemTy Nil
    ||| Cons
    |||
    ||| @elem The element to add
    ||| @rest The list for `elem` to be added to.
    (::) : (elem : elemTy x)
        -> (rest : SigmaList aTy elemTy xs)
        -> SigmaList aTy elemTy (x::xs)

||| Alisasing before syntactic sugar can be defined and added.
SList : (aTy : Type) -> (elemTy : aTy -> Type) -> List aTy -> Type
SList = SigmaList
