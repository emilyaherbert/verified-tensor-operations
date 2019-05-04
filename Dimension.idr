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
  AddThreeSL  : (ok : AddThree n Z p) -> AddThree (S n) Z     (S p)
  AddThreeSR  : (ok : AddThree Z m p) -> AddThree Z     (S m) (S p)
  AddThreeSLR : (ok : AddThree n m p) -> AddThree (S n) (S m) (S (S p))

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

%hint
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


tryAddThree : (n : Nat) -> (m : Nat) -> (p : Nat) -> Maybe (Nat, Nat, Nat)
tryAddThree Z     Z     Z         = Nothing
tryAddThree Z     Z     (S Z)     = Just (Z, Z, S Z)
tryAddThree Z     Z     (S (S k)) = Nothing
tryAddThree Z     (S k) Z         = Nothing
tryAddThree Z     (S k) (S j)     =
  case (tryAddThree Z k j) of
    Nothing        => Nothing
    Just (n, m, p) => Just (n, S m, S p)
tryAddThree (S k) Z     Z         = Nothing
tryAddThree (S k) Z     (S j)     =
  case (tryAddThree k Z j) of
    Nothing        => Nothing
    Just (n, m, p) => Just (S n, m, S p)
tryAddThree (S k) (S j) Z         = Nothing
tryAddThree (S k) (S j) (S Z)     = Nothing
tryAddThree (S k) (S j) (S (S i)) =
  case (tryAddThree k j i) of
    Nothing        => Nothing
    Just (n, m, p) => Just (S n, S m, S (S p))

tryAddThrees : Dims n -> Dims n -> Dims n -> Maybe (Dims n, Dims n, Dims n)
tryAddThrees [] [] [] = Just ([], [], [])
tryAddThrees (x :: xs) (y :: ys) (z :: zs) =
  case (tryAddThree x y z) of
    Nothing        => Nothing
    Just (n, m, p) =>
      case (tryAddThrees xs ys zs) of
        Nothing           => Nothing
        Just (ns, ms, ps) => Just (n :: ns, m :: ms, p :: ps)

--------------------------------------------------------------------------------
-- Attempts and Notes
--------------------------------------------------------------------------------

||| Given some Dims (n + m), prove you can split into Dims n and Dims m.
data Split : (n : Nat) -> (o : Dims (n + m)) -> (l : Dims n) -> (r : Dims m) -> Type where
  SZ : Split Z [] [] []
  SR : (x : Nat) -> (xs : Split Z os ls rs) -> Split Z (x :: os) ls (r :: rs)
  SL : (x : Nat) -> (xs : Split k os ls rs) -> Split (S k) (x :: os) (x :: ls) rs

dconcat : (n : Nat) -> Dims n -> Dims m -> Dims (n + m)
dconcat Z [] [] = []
dconcat Z [] ys = ys
dconcat (S k) xs [] = rewrite plusZeroRightNeutral k in xs
dconcat (S k) (x :: xs) ys = x :: (dconcat k xs ys)

data Loop : Dims n -> Dims n -> Type where
  MkLoop : (xs : Dims n) -> Loop xs xs

-- https://www.reddit.com/r/Idris/comments/9u94v8/for_types_with_custom_equality/
-- https://stackoverflow.com/questions/47545150/proof-inside-nested-constructor-of-recursive-type

--------------------------------------------------------------------------------
-- Dims reboot
--------------------------------------------------------------------------------

codata Dims2 : Nat -> Type where
  DZ : Dims2 0
  DS : (x : Nat) -> (xs : Dims2 n) -> Dims2 (S n)
  DC : (xs : Dims2 n) -> (xs' : Dims2 m) -> Dims2 (n + m)