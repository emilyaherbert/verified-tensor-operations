module Matrix

import Data.Vect

%access public export
%default total

data Matrix : (Vect n Nat) -> Type where
  MZ : (x : Double) -> Matrix []
  MS : (xs : Vect n (Matrix dims)) -> Matrix (n :: dims)

{-

Creating matrices.

-}

fill : (dims : Vect n Nat) -> Double -> (Matrix dims)
fill [] v = MZ v
fill (x :: xs) v = MS $ replicate x $ fill xs v

fillLike : {dims : Vect n Nat} -> (Matrix dims) -> Double -> (Matrix dims)
fillLike {dims} _ v = fill dims v

zerosLike : {dims : Vect n Nat} -> (Matrix dims) -> (Matrix dims)
zerosLike {dims} _ = fill dims 0.0

{-

Playing with dimensions.

-}

data Compatible : (xs : Vect n Nat) -> (ys : Vect m Nat) -> Type where
  AreCompatible : Compatible xs ys

compatible : (xs : Vect n Nat) -> (ys : Vect m Nat) -> Dec (Compatible xs ys)
compatible [] [] = Yes AreCompatible
compatible (x :: xs) [] = No absurd
compatible [] (y :: ys) = No absurd
compatible (x :: xs) (y :: ys) = ?hole

getDims : {dims : Vect n Nat} -> (Matrix dims) -> (Vect n Nat)
getDims {dims} _ = dims

compatibleDims : (Vect n Nat) -> (Vect m Nat) -> Bool
compatibleDims [] [] = True
compatibleDims (x :: xs) [] = False
compatibleDims [] (y :: ys) = False
compatibleDims (x :: xs) (y :: ys) = (x == y || x == 1 || y == 1) && (compatibleDims xs ys)

broadcastDims : (Vect n Nat) -> (Vect n Nat)

{-

Single matrix operations.

-}

elementwise : (Double -> Double) -> (Matrix dims) -> (Matrix dims)
elementwise f (MZ x) = MZ $ f x
elementwise f (MS xs) = MS $ map (elementwise f) xs

scale : Double -> (Matrix dims) -> (Matrix dims)
scale v xs = elementwise (v *) xs

{-

Two matrix operations.

-}

testMatrix1 : Matrix [10, 10]
testMatrix1 = fill [10, 10] 1.5

testMatrix2 : Matrix [10, 10]
testMatrix2 = fill [10, 10] 0.75

testMatrix3 : Matrix [10, 1]
testMatrix3 = fill [10, 1] 0.5

testMatrix4 : Matrix [10, 8, 6]
testMatrix4 = fill [10, 8, 6] 0.25