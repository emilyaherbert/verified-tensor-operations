module Dimension

import Data.Vect
import Data.HVect
import Prelude.Cast

%access public export
%default total

Dims : Nat -> Type
Dims n = Vect n Nat

data DimsView : Vect n Nat -> Type where
  MkDimsView : (xs : Vect n Nat) -> DimsView xs

-- http://cattheory.com/posts/2017-11-14-scoped-implicit-conversions.html
implicit
dimsDimsView : (xs : Vect n Nat) -> DimsView xs
dimsDimsView xs = MkDimsView xs

data DimsView2 : Nat -> Vect n Nat -> Type where
  MkDimsView2 : (xs : Vect n Nat) -> DimsView2 n xs

-- http://cattheory.com/posts/2017-11-14-scoped-implicit-conversions.html
implicit
dimsDimsView2 : (xs : Vect n Nat) -> DimsView2 n xs
dimsDimsView2 xs = MkDimsView2 xs

data FinView : Nat -> Vect n Type -> Type where
  MkFinView : (xs : Dims n) -> FinView n $ map (\x => Fin x) xs

implicit
convertToFinView : (xs : Dims n) -> FinView n $ map (\x => Fin x) xs
convertToFinView xs = MkFinView xs

data CompatibleDims : (is : Dims n) -> (js : Dims n) -> (xs : Dims n) -> Type where
  MkCompatibleDims : (is : Dims n) -> (js : Dims n) -> CompatibleDims is js $ zipWith (\x,y => x + (S j)) is js

Split : Vect n Nat -> Type
Split {n} xs = Vect n Nat

-- https://stackoverflow.com/questions/29785384/how-can-i-arrange-to-pattern-match-on-a-dependent-view
data Split2 : (n : Nat) -> Vect m ty -> Type where
  MkSplit2 : (xs : Vect n ty) -> (ys : Vect m ty) -> Split2 n (xs ++ ys)

{-
(++) : Dims n -> Dims m -> Dims (n + m)
(++) [] [] = []
(++) [] ys = ys
(++) (x :: xs) ys = x :: (Dimension.(++) xs ys)
-}

--data Dims : Nat -> Type where
--  Nil : Dims 0
--  (::) : Nat -> Dims n -> Dims (S n)
--  (++) : Dims n -> Dims m -> Dims (n + m)

--data CompatibleDims : Nat -> Type -> Type where
--  MkCompatibleDims : (dims : Dims n) -> CompatibleDims n $ HVect (map (\x => Fin x) dims)

--CompatibleDims : Dims n -> Type
--CompatibleDims xs = HVect (map (\y => Fin y) xs)

--data CompatibleDims : Dims n -> Vect n Type -> Type where
--  MkCompatibleDims : (dims : Dims n) -> CompatibleDims dims (map (\x => Fin x) dims)

--data IDims : Dims n -> Vect n Type -> Type where
--  MkIDims : (dims : Dims n) -> IDims dims $ map (\x => Fin x) dims

-- https://groups.google.com/forum/#!msg/idris-lang/038_affE4eI/kaUVyI-qCAAJ
using (from : Vect k Type, to : Vect k Type) 
  ap :
    HVect (zipWith (\dom, cod => dom -> cod) from to)
    -> HVect from 
    -> HVect to 
  ap {from = []} {to = []} []        []            = [] 
  ap {from=_::_} {to=_::_} (f :: fs) (arg :: args) = f arg :: ?rrhs --ap fs args 

res : HVect [List Char, Double]
res = ap [unpack, cos] ["hello", 0.5]

--------------------------------------------------------------------------------
-- May need ?
--------------------------------------------------------------------------------

--head : Dims (S n) -> Nat
--head (x :: xs) = x

--tail : Dims (S (S n)) -> Dims (S n)
--tail (x :: xs) = xs

--------------------------------------------------------------------------------
-- Properties
--------------------------------------------------------------------------------

-- TODO: need some property that says:
-- given dims and some dims1 that contains dims, can split dims1 into dims ++ rest

{-
concatLeftDSRightDZ :
  (xs : Dims (S n))
  -> xs ++ [] = xs
concatLeftDSRightDZ (x :: xs) = ?i_1
-}

-- https://stackoverflow.com/questions/33839427/xs-vect-n-elem-vect-n-2-elem
-- https://github.com/idris-lang/Idris-dev/blob/master/libs/prelude/Prelude/List.idr#L870
-- https://stackoverflow.com/questions/29785384/how-can-i-arrange-to-pattern-match-on-a-dependent-view

-- Data.Vect.concat : Vect m (Vect n elem) -> Vect (m * n) elem