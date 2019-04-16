module Dimension

import Data.Vect
import Data.HVect

%access public export
%default total

Dims : Nat -> Type
Dims n = Vect n Nat

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