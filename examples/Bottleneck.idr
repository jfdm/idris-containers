-- ---------------------------------------------------------- [ Bottleneck.idr ]
-- Module    : Bottleneck.idr
-- Copyright : (c) Jan de Muijnck-Hughes
-- License   : see LICENSE
-- --------------------------------------------------------------------- [ EOH ]
||| Strange bottleneck in printing.
module Bottleneck

import System
import Data.Sigma.DList
import Data.AVL.Dict

-- ---------------------------------------------------- [ Test Data Structures ]
data FTy = A | B | C | D

instance Show FTy where
  show _ = "ABCD"

data Foobar : FTy -> Type where
  Foo : Foobar A
  Bar : Foobar B
  Boo : Foobar C
  Far : Foobar D

instance Show (Foobar ty) where
  show (Foo) = "Foo"
  show (Bar) = "Bar"
  show (Boo) = "Boo"
  show (Far) = "Far"

data FWrap : Type where
  MkWrap : Foobar ty -> FWrap

instance Show FWrap where
  show (MkWrap p) = show p

-- -------------------------------------------------------------------- [ Data ]

repeat : Nat -> (Foobar ty) -> List (Foobar ty)
repeat Z     x = [x]
repeat (S n) x = x :: repeat n x

as : List (Foobar A)
as = repeat 1000 Foo

bs : List (Foobar B)
bs = repeat 1000 Bar

cs : List (Foobar C)
cs = repeat 1000 Boo

ds : (xs ** DList FTy Foobar xs)
ds = (_ ** getProof (fromList as) ++ (getProof (fromList bs)) ++ (getProof (fromList cs)))

-- ------------------------------------------------------- [ Report Generation ]

mkReport : String -> Integer -> Maybe Integer -> Integer -> String
mkReport str a Nothing z =
  unwords [ show a
          , "\t", show z
          , "\t", show (z -a)
          , "\t", "#", str]

mkReport str a (Just s) z =
  unwords [ show a
          , "\t", show s
          , "\t", show z
          , "\t", show (z - a)
          , "\t", show (s - a)
          , "\t", show (z - s)
          , "\t", "#", str]

-- ------------------------------------------------------ [ Testing Framewortk ]
harness : String -> IO (Maybe Integer) -> IO String
harness str test = do
  putStrLn str
  a <- time
  s <- test
  z <- time
  let res = mkReport str a s z
  pure res

-- ---------------------------------------------------------- [ Things to Test ]

namespace DListDict
  addMany : DList FTy Foobar xs -> Dict Nat FWrap -> Dict Nat FWrap
  addMany ds dict = snd $ DList.foldl (\(c,res),d => (S c, insert c (MkWrap d) res)) (Z,dict) ds

namespace DListDictInt
  addMany : DList FTy Foobar xs -> Dict Integer FWrap -> Dict Integer FWrap
  addMany ds dict = snd $ DList.foldl (\(c,res),d => (c+1, insert c (MkWrap d) res)) (0,dict) ds

namespace DListAssocList
  addMany : DList FTy Foobar xs -> List (Nat, FWrap) -> List (Nat, FWrap)
  addMany ds alist = snd $ DList.foldl (\(c,res),d => (S c, (c, (MkWrap d))::res)) (Z,alist) ds

namespace DListAssocListInt
  addMany : DList FTy Foobar xs -> List (Integer, FWrap) -> List (Integer, FWrap)
  addMany ds alist = snd $ DList.foldl (\(c,res),d => (c+1, (c, (MkWrap d))::res)) (0,alist) ds

namespace ListDict
  addMany : List (Foobar ty) -> Dict Nat (Foobar ty) -> Dict Nat (Foobar ty)
  addMany ds dict = snd $ foldr (\d,(c,res)=> (S c, insert c d res)) (Z,dict) ds

namespace ListDictInt
  addMany : List (Foobar ty) -> Dict Integer (Foobar ty) -> Dict Integer (Foobar ty)
  addMany ds dict = snd $ foldr (\d,(c,res)=> (c+1, insert c d res)) (0,dict) ds

namespace ListAssocList
  addMany : List (Foobar ty) -> List (Nat, (Foobar ty)) -> List (Nat, (Foobar ty))
  addMany ds dict = snd $ foldr (\d,(c,res)=> (S c, (c, d)::res)) (Z,dict) ds

namespace ListAssocListInt
  addMany : List (Foobar ty) -> List (Integer, (Foobar ty)) -> List (Integer, (Foobar ty))
  addMany ds dict = snd $ foldr (\d,(c,res)=> (c+1, (c, d)::res)) (0,dict) ds

-- --------------------------------------------------------------- [ The Tests ]

buildAndPrint : IO String
buildAndPrint = do
      r1 <- harness "Dependent List and Dict with Nat" $ do
               let d = DListDict.addMany (Sigma.getProof ds) empty
               s <- time
               printLn d
               pure (Just s)
      r2 <- harness "Dependent List and Dict with Integer" $ do
               let d = DListDictInt.addMany (Sigma.getProof ds) empty
               s <- time
               printLn d
               pure (Just s)
      r3 <- harness "Dependent List and Assoc List with Nat" $ do
               let d = DListAssocList.addMany (Sigma.getProof ds) Nil
               s <- time
               printLn d
               pure (Just s)
      r4 <- harness "Dependent List and Assoc List with Integer" $ do
               let d = DListAssocListInt.addMany (Sigma.getProof ds) Nil
               s <- time
               printLn d
               pure (Just s)
      r5 <- harness "List and Dict with Nat" $ do
               let d = ListDict.addMany (as ++ as ++ as) empty
               s <- time
               printLn d
               pure (Just s)
      r6 <- harness "List and Dict with Int" $ do
               let d = ListDictInt.addMany (as ++ as ++ as) empty
               s <- time
               printLn d
               pure (Just s)
      r7 <- harness "List and AssocList with Nat" $ do
               let d = ListAssocList.addMany (as ++ as ++ as) Nil
               s <- time
               printLn d
               pure (Just s)
      r8 <- harness "List and AssocList with Int" $ do
               let d = ListAssocListInt.addMany (as ++ as ++ as) Nil
               s <- time
               printLn d
               pure (Just s)
      pure $unlines [r1,r2,r3,r4,r5,r6,r7,r8]

justBuild : IO String
justBuild = do
      r1 <- harness "Dependent List and Dict with Nat" $ do
               let d = DListDict.addMany (Sigma.getProof ds) empty
               pure Nothing
      r2 <- harness "Dependent List and Dict with Integer" $ do
               let d = DListDictInt.addMany (Sigma.getProof ds) empty
               s <- time
               pure Nothing
      r3 <- harness "Dependent List and Assoc List with Nat" $ do
               let d = DListAssocList.addMany (Sigma.getProof ds) Nil
               s <- time
               pure Nothing
      r4 <- harness "Dependent List and Assoc List with Integer" $ do
               let d = DListAssocListInt.addMany (Sigma.getProof ds) Nil
               s <- time
               pure Nothing
      r5 <- harness "List and Dict with Nat" $ do
               let d = ListDict.addMany (as ++ as ++ as) empty
               s <- time
               pure Nothing
      r6 <- harness "List and Dict with Int" $ do
               let d = ListDictInt.addMany (as ++ as ++ as) empty
               s <- time
               pure Nothing
      r7 <- harness "List and AssocList with Nat" $ do
               let d = ListAssocList.addMany (as ++ as ++ as) Nil
               s <- time
               pure Nothing
      r8 <- harness "List and AssocList with Int" $ do
               let d = ListAssocListInt.addMany (as ++ as ++ as) Nil
               s <- time
               pure Nothing
      pure $ unlines [r1,r2,r3,r4,r5,r6,r7,r8]

-- --------------------------------------------------------------- [ Execution ]
namespace Main
    main : IO ()
    main = do
      putStrLn "-- ------------------------------------------------------------------------ [  ]"
      report <- buildAndPrint
      putStrLn "Building and Printing"
      putStrLn "Start\tSplit\tStop\tTotal\tBuild\tPrint"
      putStrLn report
      putStrLn "--  ------------------------------------------------------------------------ [  ]"
      report <- justBuild
      putStrLn "Just Building"
      putStrLn $ "Start\tStop\tTotal"
      putStrLn report

-- --------------------------------------------------------------------- [ EOF ]
