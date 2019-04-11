module Dimension

import Data.Vect

%access public export
%default total

data Dims : Nat -> Type where
  DZ : Dims 0
  DS : (d : Nat) -> (ds : Dims n) -> Dims (S n)

DimsType : Vect n Nat -> Dims n
DimsType [] = DZ
DimsType (x :: xs) = DS x $ DimsType xs

{-

Interface implementations.

-}

Eq (Dims n) where
  (==) DZ DZ = True
  (==) (DS x xs) (DS y ys) = (x == y) && (xs == ys)

{-
-- https://github.com/edwinb/TypeDD-Samples/blob/master/Chapter8/Exercises/ex_8_3.idr
headUnequal :
  {xs : Dims n}
  -> {ys : Dims n}
  -> (contra : (x = y) -> Void)
  -> (DS x xs) = (DS y ys) -> Void
headUnequal contra Refl = contra Refl

tailUnequal :
  {xs : Dims n}
  -> {ys : Dims n}
  -> (contra : (xs = ys) -> Void)
  -> (DS x xs) = (DS y ys) -> Void
tailUnequal contra Refl = contra Refl

DecEq (Dims n) where
  decEq DZ DZ = Yes Refl
  decEq (DS x xs) (DS y ys) = case decEq x y of
                                  No contra => No (headUnequal contra)
                                  Yes Refl => case decEq xs ys of
                                                Yes Refl => Yes Refl
                                                No contra => No (tailUnequal contra)
-}

head : Dims (S n) -> Nat
head (DS x xs) = x

tail : Dims (S n) -> Dims n
tail (DS x xs) = xs

index : Nat -> Dims (S n) -> Dims n
index i (DS x xs) = xs

indexPf :
  (n : Nat)
  -> (xs : Dims (S m))
  -> {auto headOk : LTE (S n) (head xs)}  
  -> Dims m
indexPf n (DS x xs) = xs

indexMaybe : (n : Nat) -> Dims (S n) -> Maybe $ Dims n
indexMaybe n (DS x xs) =
  case lte n x of
       False => Nothing
       True => Just xs

indexMany : (is : Vect n Nat) -> Dims (n + (S m)) -> Dims (S m)
indexMany [] xs = xs
indexMany (i :: is) (DS n dims) = indexMany is dims

slice :
  (start : Nat)
  -> (stop : Nat)
  -> Dims (S n)
  -> {auto ok : LTE (S start) stop}
  -> Dims (S n)
slice Z Z (DS n dims) {ok} impossible
slice Z (S k) (DS n dims) {ok} = DS (S k) dims
slice (S k) Z (DS n dims) {ok} impossible
slice (S k) (S j) (DS n dims) {ok} = DS (minus (S j) (S k)) dims

slicePf :
  (start : Nat)
  -> (stop : Nat)
  -> (xs : Dims (S n))
  -> {auto smaller : LTE (S start) stop}
  -> {auto headOk : LTE stop (head xs)}
  -> Dims (S n)
slicePf Z Z _ impossible
slicePf (S k) Z _ impossible
slicePf Z (S j) (DS x xs) = DS (S j) xs
slicePf (S k) (S j) (DS x xs) = DS (minus (S j) (S k)) xs

canBeBroadcast : Dims n -> Dims m -> Bool
canBeBroadcast DZ DZ = True
canBeBroadcast DZ (DS y ys) = True
canBeBroadcast (DS x xs) DZ = True
canBeBroadcast (DS x xs) (DS y ys) = (x == y || x == 1 || y == 1) && (canBeBroadcast xs ys)

broadcast : (xs : Dims n) -> (ys : Dims m) -> {auto ok : canBeBroadcast xs ys = True} -> Dims (max n m)
broadcast DZ DZ = DZ
broadcast DZ (DS y ys) = DS y ys
broadcast (DS x xs) DZ = DS x xs
broadcast (DS x xs) (DS y ys) = ?hole


test1 : Dims 4
test1 = DS 10 $ DS 10 $ DS 10 $ DS 10 DZ