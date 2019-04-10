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

head : Dims (S n) -> Nat
head (DS x xs) = x

tail : Dims (S n) -> Dims n
tail (DS x xs) = xs

index : Nat -> Dims (S n) -> Dims n
index i (DS x xs) = xs

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