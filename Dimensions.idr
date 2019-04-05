module Dimensions

import Data.Vect

%access public export
%default total

data Dims : Nat -> Type where
  DZ : Dims 0
  DS : (d : Nat) -> (ds : Dims n) -> Dims (S n)