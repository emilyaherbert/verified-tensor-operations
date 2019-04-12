module Dimension

import Data.Vect

%access public export
%default total

Dims : Nat -> Type
Dims n = Vect n Nat

{-

Interface implementations.

-}

head : Dims (S n) -> Nat
head (x :: xs) = x

tail : Dims (S (S n)) -> Dims (S n)
tail (x :: xs) = xs