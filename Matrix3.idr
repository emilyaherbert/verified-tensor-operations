module Matrix

import Data.Vect

%access public export
%default total

data Matrix : (List Nat) -> Type where
  MZ : (x : Double) -> Matrix []
  MS : (xs : List (Matrix dims)) -> Matrix ((length xs) :: dims)

{-

Creating matrices.

-}

fill : (dims : List Nat) -> Double -> (Matrix dims)
fill [] v = MZ v
fill (x :: xs) v = MS $ replicate x $ fill xs v

fillLike : {dims : List Nat} -> (Matrix dims) -> Double -> (Matrix dims)
fillLike {dims} _ v = fill dims v

zerosLike : {dims : List Nat} -> (Matrix dims) -> (Matrix dims)
zerosLike {dims} _ = fill dims 0.0