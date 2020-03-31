module Data.AVL.Core.Quantifiers

import public Data.Tree
import public Data.AVL.Core
import public Data.AVL.Core.API

%default total
%access export

namespace AVL
  namespace Keys

    public export
    data HasKey : (key : typeKey)
               -> (tree : AVLTree h typeKey typeValue)
               -> Type
      where
        IsKey : (prf : IsKeyIn key (Subset.getWitness avl))
             -> HasKey key avl

    keyNotInAVlTree : (contra : IsKeyIn key tree -> Void)
                   -> HasKey key (Element tree prf)
                   -> Void
    keyNotInAVlTree contra (IsKey x) = contra x

    isKey : DecEq typeKey
         => (key : typeKey)
         -> (tree : AVLTree h typeKey typeValue)
         -> Dec (HasKey key tree)
    isKey key (Element tree prf) with (isKey key tree)
      isKey key (Element tree prf) | (Yes x) = Yes (IsKey x)
      isKey key (Element tree prf) | (No contra) = No (keyNotInAVlTree contra)

    public export
    data All : (predicate : typeKey -> Type)
            -> (tree : AVLTree h typeKey typeValue)
            -> Type
      where
        MkProof : (prf : Tree.Keys.All p (Subset.getWitness avl))
               -> All p avl

  namespace Values


    public export
    data HasValue : (value : typeValue)
                 -> (tree : AVLTree h typeKey typeValue)
                 -> Type
      where
        IsValue : (prf : IsValueIn value (Subset.getWitness avl))
               -> HasValue value avl

    valueNotInAVLTree : (contra : IsValueIn value tree -> Void)
                     -> HasValue value (Element tree prf)
                     -> Void
    valueNotInAVLTree contra (IsValue prf) = contra prf

    isValue : DecEq typeValue
           => (value : typeValue)
           -> (tree : AVLTree h typeKey typeValue)
           -> Dec (HasValue value tree)
    isValue value (Element tree prf) with (isValue value tree)
      isValue value (Element tree prf) | (Yes x) = Yes (IsValue x)
      isValue value (Element tree prf) | (No contra) = No (valueNotInAVLTree contra)


    public export
    data All : (predicate : typeValue -> Type)
            -> (tree : AVLTree h typeKey typeValue)
            -> Type
      where
        MkProof : (prf : Tree.Values.All p (Subset.getWitness avl))
               -> AVL.Values.All p avl

  namespace KVPairs


    public export
    data All : (predicate : typeKey -> typeValue -> Type)
            -> (tree : AVLTree k typeKey typeValue)
            -> Type
      where
        MkProof : (prf : Tree.KVPairs.All p (Subset.getWitness avl))
                -> All p avl
