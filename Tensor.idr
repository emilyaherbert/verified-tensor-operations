module Tensor

import Data.Vect
import Dimension

%access public export
%default total

data Tensor : Dims n -> Type -> Type where
  TZ : (x : ty) -> Tensor [] ty
  TS : (xs : Vect n (Tensor dims ty)) -> Tensor (n :: dims) ty

get_dims : {dims : Dims n} -> Tensor dims a -> Dims n
get_dims {dims} _ = dims

--------------------------------------------------------------------------------
-- Building
--------------------------------------------------------------------------------

fill : ty -> (dims : Dims n) -> Tensor dims ty
fill v [] = TZ v
fill v (x :: xs) = TS $ replicate x $ fill v xs

fillLike : ty1 -> Tensor dims ty2 -> Tensor dims ty1
fillLike v xs = fill v $ get_dims xs

--------------------------------------------------------------------------------
-- Interfaces
--------------------------------------------------------------------------------

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

--------------------------------------------------------------------------------
-- Combine-two
--------------------------------------------------------------------------------

zipWith : (a -> b -> c) -> Tensor dims a -> Tensor dims b -> Tensor dims c
zipWith f (TZ x) (TZ y) = TZ $ f x y
zipWith f (TS xs) (TS ys) = TS $ Data.Vect.zipWith (Tensor.zipWith f) xs ys

plus : Num a => Tensor dims a -> Tensor dims a -> Tensor dims a
plus xs ys = Tensor.zipWith (+) xs ys

(+) : Num a => Tensor dims a -> Tensor dims a -> Tensor dims a
(+) xs ys = plus xs ys

minus : Num a => Neg a => Tensor dims a -> Tensor dims a -> Tensor dims a
minus xs ys = plus xs $ map ((-1) *) ys

(-) : Num a => Neg a => Tensor dims a -> Tensor dims a -> Tensor dims a
(-) xs ys = minus xs ys

mult : Num a => Tensor dims a -> Tensor dims a -> Tensor dims a
mult xs ys = Tensor.zipWith (*) xs ys

(*) : Num a => Tensor dims a -> Tensor dims a -> Tensor dims a
(*) xs ys = mult xs ys

div : Num a => Fractional a => Tensor dims a -> Tensor dims a -> Tensor dims a
div xs ys = Tensor.zipWith (/) xs ys

(/) : Num a => Fractional a => Tensor dims a -> Tensor dims a -> Tensor dims a
(/) xs ys = div xs ys

concat : Tensor (n :: dims) ty -> Tensor (m :: dims) ty -> Tensor (n + m :: dims) ty
concat (TS xs) (TS ys) = TS $ xs ++ ys

(++) : Tensor (n :: dims) ty -> Tensor (m :: dims) ty -> Tensor (n + m :: dims) ty
(++) xs ys = concat xs ys

--------------------------------------------------------------------------------
-- Indexing
--------------------------------------------------------------------------------

index :
  Fin n
  -> Tensor (n :: dims) ty
  -> Tensor dims ty
index i (TS xs) = Data.Vect.index i xs

slice :
  (start : Nat)
  -> (count : Nat)
  -> Tensor (start + (count + m) :: dims) ty
  -> Tensor (count :: dims) ty
slice start count (TS xs) = TS $ Data.Vect.take count $ Data.Vect.drop start xs

flatten :
  Tensor (n :: m :: dims) ty
  -> Tensor (n * m :: dims) ty

--------------------------------------------------------------------------------
-- Properties
--------------------------------------------------------------------------------

min : Ord ty => ty -> Tensor dims ty -> ty
min acc xs = foldl (\a,e => if a < e then a else e) acc xs

max : Ord ty => ty -> Tensor dims ty -> ty
max acc xs = foldl (\a,e => if a > e then a else e) acc xs

--------------------------------------------------------------------------------
-- Testers
--------------------------------------------------------------------------------

test1 : Tensor [10, 10] Double
test1 = Tensor.fill 0.5 [10, 10]

test2 : Tensor [10, 10] Double
test2 = Tensor.fill 1.5 [10, 10]

test3 : Tensor [10, 10, 10] Double
test3 = Tensor.fill 1.0 [10, 10, 10]