module Dimension

import Data.Vect
import Data.HVect
import Prelude.Cast

%access public export
%default total

Dims : Nat -> Type
Dims n = Vect n Nat

data PosDims : Nat -> Type where
  Nil : PosDims 0
  (::) : (x : Nat) -> {auto ok : IsSucc x} -> (xs : PosDims n) -> PosDims (S n)

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
  AddThreeZ : AddThree Z Z Z
  AddThreeSLR : (ok : AddThree n m p) -> AddThree (S n) (S m) (S (S p))
  AddThreeSL  : (ok : AddThree n Z p) -> AddThree (S n) Z     (S p)
  AddThreeSR  : (ok : AddThree Z m p) -> AddThree Z     (S m) (S p)

data AddThrees : Dims n -> Dims n -> Dims n -> Type where
  AddThreesZ : AddThrees [] [] []
  AddThreesS : (ok : AddThree n m p) -> AddThrees ns ms ps -> AddThrees (n :: ns) (m :: ms) (p :: ps)

leftTooBig : Not (AddThree (S n) m Z)
leftTooBig AddThreeZ impossible

rightTooBig : Not (AddThree n (S m) Z)
rightTooBig AddThreeZ impossible

leftRightTooBig : Not (AddThree (S n) (S m) Z)
leftRightTooBig AddThreeZ impossible

leftRightTooBig' : Not (AddThree (S n) (S m) (S Z))
leftRightTooBig' AddThreeZ impossible

goalTooBig : Not (AddThree Z Z (S p))
goalTooBig AddThreeZ impossible

fromLeftSucc : AddThree (S n) Z (S p) -> AddThree n Z p
fromLeftSucc (AddThreeSL next) = next

fromRightSucc : AddThree Z (S m) (S p) -> AddThree Z m p
fromRightSucc (AddThreeSR next) = next

fromLeftRightSucc : AddThree (S n) (S m) (S (S p)) -> AddThree n m p
fromLeftRightSucc (AddThreeSLR ok) = ok

canAddThree : (n : Nat) -> (m : Nat) -> (p : Nat) -> Dec (AddThree n m p)
canAddThree Z     Z     Z       = Yes AddThreeZ
canAddThree Z     Z     (S p)   = No goalTooBig
canAddThree Z     (S m) Z       = No rightTooBig
canAddThree Z     (S m) (S p)     with (canAddThree Z m p)
  canAddThree Z     (S m) (S p) | (Yes prf)   = Yes (AddThreeSR prf)
  canAddThree Z     (S m) (S p) | (No contra) = No (contra . fromRightSucc)
canAddThree (S n) Z     Z       = No leftTooBig
canAddThree (S n) Z     (S p)     with (canAddThree n Z p)
  canAddThree (S n) Z     (S p) | (Yes prf)   = Yes (AddThreeSL prf)
  canAddThree (S n) Z     (S p) | (No contra) = No (contra . fromLeftSucc)
canAddThree (S n) (S m) Z       = No leftRightTooBig
canAddThree (S n) (S m) (S Z)   = No leftRightTooBig'
canAddThree (S n) (S m) (S (S p)) with (canAddThree n m p)
  canAddThree (S n) (S m) (S (S p)) | (Yes prf)   = Yes (AddThreeSLR prf)
  canAddThree (S n) (S m) (S (S p)) | (No contra) = No (contra . fromLeftRightSucc)