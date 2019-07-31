-- ------------------------------------------------------------ [ DeBruijn.idr ]
-- Module    : DeBruijn.idr
-- Copyright : (c) 2015,2016 See CONTRIBUTORS.md
-- License   : see LICENSE
-- --------------------------------------------------------------------- [ EOH ]
||| Data structure to compute de Bruijn indices.
|||
||| Thanks to christiansen's Galois tutorials for the accessor and
||| mutator functions for environments/object store.
module Data.DeBruijn

import Data.DList

%default total
%access public export

||| A de Bruijn Index.
|||
||| @T    The type of type's collected.
||| @ctxt The collection of types.
||| @t    The element collected at the current position.
public export
data Index : (T : Type)
          -> (ctxt : List T)
          -> (t : T)
          -> Type where
  ||| The first element in the index.
  First : Index ty (t::ts) t

  ||| The next element in the index.
  Next  : Index ty ts t -> Index ty (t'::ts) t


indexEmpty : DecEq type => Index type [] t -> Void
indexEmpty First impossible
indexEmpty (Next _) impossible

notInIndex : DecEq type
          => (contra : (t = x) -> Void)
          -> (f : Index type xs t -> Void)
          -> Index type (x :: xs) t
          -> Void
notInIndex contra f First = contra Refl
notInIndex contra f (Next x) = f x

isIndex : DecEq type
       => (t : type)
       -> (ctxt : List type)
       -> Dec (Index type ctxt t)
isIndex t [] = No indexEmpty
isIndex t (x :: xs) with (decEq t x)
  isIndex x (x :: xs) | (Yes Refl) = Yes First
  isIndex t (x :: xs) | (No contra) with (isIndex t xs)
    isIndex t (x :: xs) | (No contra) | (Yes prf) = Yes (Next prf)
    isIndex t (x :: xs) | (No contra) | (No f) = No (notInIndex contra f)


||| Sometimes it is bettern to think that we have this thing called an
||| environment and not a `DList`.
|||
||| @t    The Type for Types in our environment.
||| @obj  How we interpret the types in our DSL. Either this is a
|||       dependent type or a function that computes a type.
||| @ctxt The typing context.
public export
Env : (t : Type) -> (obj : t -> Type) -> (ctxt : List t) -> Type
Env ty obj ctxt = DList ty (\x => obj x) ctxt

||| Add an object from our typing environment.
||| @env The typing environment.
export
extend : {t : ty}
      -> (env : Env ty e ctxt)
      -> (obj : e t)
      -> Env ty e (t::ctxt)
extend env obj = obj :: env

||| Read an object from our typing environment.
|||
||| @idx The typing context.
||| @env The typing environment.
export
read : (idx : Index ty ctxt t)
    -> (env : Env ty e ctxt)
    -> e t
read First    (obj::store) = obj
read (Next x) (obj::store) = read x store

||| Add an object to our typnig environment.
|||
||| @idx The typing context.
||| @obj The object to add.
||| @env The environment to which the object is added.
export
update : (idx : Index ty ctxt t )
      -> (obj : e t)
      -> (env : Env ty e ctxt)
      -> Env ty e ctxt
update First    obj (_    :: store) = obj  :: store
update (Next x) obj (obj' :: store) = obj' :: update x obj store


-- --------------------------------------------------------------------- [ EOF ]
