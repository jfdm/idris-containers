||| Data structure to compute de Bruijn indices.
|||
module Data.DeBruijn

import Data.DList

||| A de Bruijn Index.
|||
||| @T    The type of type's collected.
||| @ctxt The collection of types.
||| @t    The element collected at the current position.
public export
data TypeIndex : (T : Type)
              -> (ctxt : List T)
              -> (t : T)
              -> Type where
  ||| The first element in the index.
  First : TypeIndex ty (t::ts) t

  ||| The next element in the index.
  Next  : TypeIndex ty ts t -> TypeIndex ty (t'::ts) t

%fragile TypeIndex "Undecided about the name; it might change. sorry."

public export
Env : (t : Type) -> (obj : t -> Type) -> (ctxt : List t) -> Type
Env = DList

|||
export
read : TypeIndex ty ctxt t -> Env ty e ctxt -> e t
read First    (obj::store) = obj
read (Next x) (obj::store) = read x store

export
write : TypeIndex ty ctxt t -> e t -> Env ty e ctxt -> Env ty e ctxt
write First    obj (_    :: store) = obj  :: store
write (Next x) obj (obj' :: store) = obj' :: write x obj store
