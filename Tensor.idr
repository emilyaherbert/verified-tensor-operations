module Tensor

{-

: Matrix [3,3] Double
TS [TS [TZ 0.0, TZ 1.0],
    TS [TZ 2.0, TZ 3.0],
    TS [TZ 4.0, TZ 5.0]]

Foldable operations:
sum t
product t

Elementwise operations:
map (5 +) t

Combination operations:
// TODO: broadcasting
t1 + t2

-}

import Data.Vect

%access public export
%default total

Dims : Nat -> Type
Dims n = Vect n Nat

data Tensor : Dims n -> Type -> Type where
  TZ : (x : ty) -> Tensor [] ty
  TS : (xs : Vect n (Tensor dims ty)) -> Tensor (n :: dims) ty

fill : (dims : Dims n) -> ty -> Tensor dims ty
fill [] v = TZ v
fill (x :: xs) v = TS $ replicate x $ fill xs v

zeros : (dims : Dims n) -> Tensor dims Double
zeros xs = fill xs 0.0

{-

Interface implementations.

-}

Eq ty => Eq (Tensor dims ty) where
  (==) (TZ x) (TZ y) = x == y
  (==) (TS xs) (TS ys) = foldl (\acc,elem => acc && elem) True $ zipWith (\x,y => x == y) xs ys

Functor (Tensor dims) where
  map func (TZ x) = TZ $ func x
  map func (TS xs) = TS $ map (map func) xs

Foldable (Tensor dims) where
  foldr func acc (TZ x) = func x acc
  foldr func acc (TS xs@((TZ y) :: ys)) = foldr (\(TZ e),a => func e a) acc xs
  foldr func acc (TS xs) = foldr (\e,a => foldr func a e) acc xs

  foldl func acc (TZ x) = func acc x
  foldl func acc (TS xs@((TZ y) :: ys)) = foldl (\a,(TZ e) => func a e) acc xs
  foldl func acc (TS xs) = foldl (\a,e => foldl func a e) acc xs

interface Aggregatable (t : Type -> Type) where
  aggregater : (elem -> acc -> acc) -> (acc -> acc -> acc) -> acc -> t elem -> acc
  aggregatel : (acc -> elem -> acc) -> (acc -> acc -> acc) -> acc -> t elem -> acc

Aggregatable (Tensor dims) where
  aggregater seqOp combOp acc (TZ x) = seqOp x acc
  aggregater seqOp combOp acc (TS xs@((TZ y) :: ys)) = foldr (\(TZ e),a => seqOp e a) acc xs
  aggregater seqOp combOp acc (TS xs) = foldr (\e,a => combOp e a) acc $ map (aggregater seqOp combOp acc) xs

  aggregatel seqOp combOp acc (TZ x) = seqOp acc x
  aggregatel seqOp combOp acc (TS xs@((TZ y) :: ys)) = foldl (\a,(TZ e) => seqOp a e) acc xs
  aggregatel seqOp combOp acc (TS xs) = foldl (\a,e => combOp a e) acc $ map (aggregatel seqOp combOp acc) xs

{-

Dimensionality functions.

-}

canBeBroadcast : Dims n -> Dims m -> Bool
canBeBroadcast [] [] = True
canBeBroadcast [] (y :: ys) = True
canBeBroadcast (x :: xs) [] = True
canBeBroadcast (x :: xs) (y :: ys) = (x == y || x == 1 || y == 1) && (canBeBroadcast xs ys)

broadcast : (xs : Dims n) -> (ys : Dims m) -> {auto ok : canBeBroadcast xs ys = True} -> Dims p

{-

Combine-two functions.

-}

zipWith : (a -> b -> c) -> Tensor dims a -> Tensor dims b -> Tensor dims c
zipWith f (TZ x) (TZ y) = TZ $ f x y
zipWith f (TS xs) (TS ys) = TS $ Data.Vect.zipWith (Tensor.zipWith f) xs ys

add : Num a => Tensor dims a -> Tensor dims a -> Tensor dims a
add xs ys = Tensor.zipWith (+) xs ys

(+) : Num a => Tensor dims a -> Tensor dims a -> Tensor dims a
(+) xs ys = add xs ys

sub : Num a => Neg a => Tensor dims a -> Tensor dims a -> Tensor dims a
sub xs ys = add xs $ map ((-1) *) ys

(-) : Num a => Neg a => Tensor dims a -> Tensor dims a -> Tensor dims a
(-) xs ys = sub xs ys

mult : Num a => Tensor dims a -> Tensor dims a -> Tensor dims a
mult xs ys = Tensor.zipWith (*) xs ys

(*) : Num a => Tensor dims a -> Tensor dims a -> Tensor dims a
(*) xs ys = mult xs ys

div : Num a => Fractional a => Tensor dims a -> Tensor dims a -> Tensor dims a
div xs ys = Tensor.zipWith (/) xs ys

(/) : Num a => Fractional a => Tensor dims a -> Tensor dims a -> Tensor dims a
(/) xs ys = div xs ys

{-

Toy examples.

-}

test1 : Tensor [10, 10] Double
test1 = fill [10, 10] 0.5

test2 : Tensor [10, 10] Double
test2 = fill [10, 10] 1.5

test3 : Tensor [10, 10, 10] Double
test3 = fill [10, 10, 10] 1.0