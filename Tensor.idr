module Tensor

{-

: Tensor (DimsType [3,3]) Double
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
import Dimension

%access public export
%default total

data Tensor : Dims n -> Type -> Type where
  TZ : (x : ty) -> Tensor DZ ty
  TS : (xs : Vect n (Tensor dims ty)) -> Tensor (DS n dims) ty

fill : ty -> (dims : Dims n) -> Tensor dims ty
fill v DZ = TZ v
fill v (DS x xs) = TS $ replicate x $ fill v xs

zeros : (dims : Dims n) -> Tensor dims Double
zeros xs = fill 0.0 xs

get_dims : {dims : Dims n} -> Tensor dims a -> Dims n
get_dims {dims} _ = dims

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

Indexing.

-}

vectIndex : (i : Nat) -> Vect n a -> Maybe a
vectIndex Z [] = Nothing
vectIndex Z (x :: xs) = Just x
vectIndex (S k) [] = Nothing
vectIndex (S k) (x :: xs) = vectIndex k xs

index :
  (i : Nat)
  -> {dims : Dims (S n)}
  -> Tensor dims a
  -> Maybe $ Tensor (index i dims) a
index i (TS xs) = vectIndex i xs

indexMany :
  (is : Vect n Nat)
  -> {dims : Dims (n + (S m))}
  -> Tensor dims a
  -> Maybe $ Tensor (indexMany is dims) a
indexMany [] (TS ts) = Just $ TS ts
indexMany (x :: xs) (TS ts) =
  case index x (TS ts) of
       Nothing => Nothing
       Just ys => indexMany xs ys

vectTake : (n : Nat) -> Vect m a -> Maybe $ Vect n a
vectTake Z _ = Just []
vectTake (S k) [] = Nothing
vectTake (S k) (x :: xs) =
  case vectTake k xs of
       Nothing => Nothing
       Just ys => Just $ x :: ys

vectSlice :
  (start : Nat)
  -> (stop : Nat)
  -> Vect n a
  -> {auto ok : LTE (S start) stop}
  -> Maybe $ Vect ((-) stop start {smaller = lteSuccLeft ok}) a
vectSlice Z     Z     _         {ok} impossible
vectSlice Z     (S k) xs        {ok} = vectTake (S k) xs
vectSlice (S k) Z     _         {ok} impossible
vectSlice (S k) (S j) []        {ok} = Nothing
vectSlice (S k) (S j) (x :: xs) {ok} = vectSlice k j xs {ok = fromLteSucc ok}

slice :
  (start : Nat)
  -> (stop : Nat)
  -> {dims : Dims (S n)}
  -> Tensor dims a
  -> {auto ok : LTE (S start) stop}
  -> Maybe $ Tensor (slice start stop dims {ok = ok}) a
slice Z     Z     _       {ok} impossible
slice Z     (S j) (TS xs) {ok} =
  case vectTake (S j) xs of
       Nothing => Nothing
       Just ys => Just $ TS ys
slice (S k) Z     _       {ok} impossible
slice (S k) (S j) (TS []) {ok} = Nothing
slice (S k) (S j) (TS xs) {ok} =
  case vectSlice (S k) (S j) xs {ok = ok} of
       Nothing => Nothing
       Just ys => Just $ TS ys

{-

Combine-two functions.

-}

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

{-

testers...

-}

test1 : Tensor (DimsType [10, 10]) Double
test1 = fill 0.5 $ DimsType [10, 10]

test2 : Tensor (DimsType [10, 10]) Double
test2 = fill 1.5 $ DimsType [10, 10]

test3 : Tensor (DimsType [10, 10, 10]) Double
test3 = fill 1.0 $ (DimsType [10, 10, 10])