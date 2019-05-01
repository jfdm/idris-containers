module Data.BVect

%default total
%access public export

data BVect : (u,c : Nat) -> Type -> Type where
  Nil : BVect n 0 type
  Add : (x : type)
     -> (prf : LTE (S c) n)
     -> BVect n c type
     -> BVect n (S c) type

namespace API
  (::) : (x : type) -> {auto prf : LTE (S c) n} -> BVect n c type -> BVect n (S c) type
  (::) x rest {prf} = Add x prf rest
