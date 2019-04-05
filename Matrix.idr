module Matrix

import Data.Vect

total
containsZero : (Vect n Nat) -> Bool
containsZero [] = False
containsZero (x :: xs) = if x == 0 then True else False

total
Matrix : (dims: Vect n Nat) -> Type
Matrix [] = Double
Matrix (x :: xs) = Vect x $ Matrix xs

total
fill : (dims : Vect n Nat) -> Double -> (Matrix dims)
fill [] v = v
fill (x :: xs) v = replicate x $ fill xs v

total
fillLike : {dims : Vect n Nat} -> (Matrix dims) -> Double -> (Matrix dims)
fillLike {dims} _ v = fill dims v

total
zerosLike : {dims : Vect n Nat} -> (Matrix dims) -> (Matrix dims)
zerosLike {dims} _ = fill dims 0.0

total
getDims : {dims : Vect n Nat} -> (Matrix dims) -> (Vect n Nat)
getDims {dims} _ = dims

total
compatibleDims : (Vect n Nat) -> (Vect n Nat) -> Bool
compatibleDims [] [] = True
compatibleDims (x :: xs) (y :: ys) = (x == y || x == 1 || y == 1) && (compatibleDims xs ys)

total
elementwise :
  (Double -> Double)
  -> {dims : Vect n Nat}
  -> (Matrix dims)
  -> (Matrix dims)
elementwise {dims = []} f x = f x
elementwise {dims = (d :: ds)} f xs = map (elementwise f) xs

total
e2 : (Double -> Double) -> (Matrix dims) -> (Matrix dims)

total
combineTwo :
  (Double -> Double -> Double)
  -> {dims : Vect n Nat}
  -> (Matrix dims)
  -> (Matrix dims)
  -> (Matrix dims)
combineTwo {dims = []} f x y = f x y
combineTwo {dims = (d :: ds)} f xs ys = zipWith (combineTwo f) xs ys

total
add :
  {dims : Vect n Nat}
  -> (Matrix dims)
  -> (Matrix dims)
  -> (Matrix dims)
add xs ys = combineTwo (+) xs ys

total
(+) :
  {dims : Vect n Nat}
  -> (Matrix dims)
  -> (Matrix dims)
  -> (Matrix dims)
(+) xs ys = add xs ys

total
subtract :
  {dims : Vect n Nat}
  -> (Matrix dims)
  -> (Matrix dims)
  -> (Matrix dims)
subtract xs ys = combineTwo (-) xs ys

total
(-) :
  {dims : Vect n Nat}
  -> (Matrix dims)
  -> (Matrix dims)
  -> (Matrix dims)
(-) xs ys = subtract xs ys

total
multiply :
  {dims : Vect n Nat}
  -> (Matrix dims)
  -> (Matrix dims)
  -> (Matrix dims)
multiply xs ys = combineTwo (*) xs ys

total
(*) :
  {dims : Vect n Nat}
  -> (Matrix dims)
  -> (Matrix dims)
  -> (Matrix dims)
(*) xs ys = multiply xs ys

total
divide :
  {dims : Vect n Nat}
  -> (Matrix dims)
  -> (Matrix dims)
  -> (Matrix dims)
divide xs ys = combineTwo (/) xs ys

total
(/) :
  {dims : Vect n Nat}
  -> (Matrix dims)
  -> (Matrix dims)
  -> (Matrix dims)
(/) xs ys = divide xs ys

total
scalar :
  Double
  -> {dims : Vect n Nat}
  -> (Matrix dims)
  -> (Matrix dims)
scalar v xs = elementwise (\x => x * v) xs

testMatrix1 : Matrix [10, 10]
testMatrix1 = fill [10, 10] 0.5

testMatrix2 : Matrix [10, 3, 4]
testMatrix2 = fill [10, 3, 4] 0.24