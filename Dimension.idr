module Dimension

import Data.Vect
import Data.HVect
import Prelude.Cast

%access public export
%default total

Dims : Nat -> Type
Dims n = Vect n Nat

--------------------------------------------------------------------------------
-- DimsView
--------------------------------------------------------------------------------

data DimsView : Nat -> Dims n -> Type where
  MkDimsView : (xs : Dims n) -> DimsView n xs

-- http://cattheory.com/posts/2017-11-14-scoped-implicit-conversions.html
implicit
toDimsView : (xs : Dims n) -> DimsView n xs
toDimsView xs = MkDimsView xs

implicit
fromDimsView : (xs : DimsView n xs') -> Dims n
fromDimsView (MkDimsView xs') = xs'

--------------------------------------------------------------------------------
-- Properties
--------------------------------------------------------------------------------

data AddThree : Nat -> Nat -> Nat -> Type where
  AddThreeZ : AddThree 0 1 1 -- 0 0 0. Has to be this way because of how indices work in arrayland.
  AddThreeSL : (ok : AddThree n m p) -> AddThree (S n) m     (S p)
  AddThreeSR : (ok : AddThree n m p) -> AddThree n     (S m) (S p)

data AddThrees : Dims n -> Dims n -> Dims n -> Type where
  AddThreesZ : AddThrees [] [] []
  AddThreesS : (ok : AddThree n m p) -> AddThrees ns ms ps -> AddThrees (n :: ns) (m :: ms) (p :: ps)