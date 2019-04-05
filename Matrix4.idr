module Matrix

import Data.Vect

%access public export
%default total

data Matrix : Vect n Nat -> Type -> Type where
  MZ : (x : ty) -> Matrix [] ty
  MS : (xs : Vect (S n) (Matrix dims ty)) -> Matrix ((S n) :: dims) ty

Eq ty => Eq (Matrix dims ty) where
  (==) (MZ x) (MZ y) = x == y
  (==) (MS xs) (MS ys) = foldl (\acc,elem => acc && elem) True $ zipWith (\x,y => x == y) xs ys

Functor (Matrix dims) where
  map func (MZ x) = MZ $ func x
  map func (MS xs) = MS $ map func xs


{-
fill : Eq ty => (dims : Vect n Nat) -> (v : ty) -> Matrix dims ty
fill [] v = MZ v
fill (x :: xs) v = MS $ replicate x $ fill xs v













testMatrix1 : Matrix [10, 10] Double
testMatrix1 = fill [10, 10] 1.5

testMatrix2 : Matrix [10, 10] Double
testMatrix2 = fill [10, 10] 0.75

testMatrix3 : Matrix [10, 1] Double
testMatrix3 = fill [10, 1] 0.5

testMatrix4 : Matrix [10, 8, 6] Double
testMatrix4 = fill [10, 8, 6] 0.25
-}