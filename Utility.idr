import Data.Vect
import Data.HVect

vectInjective1 :
  {xs : Vect n a}
  -> {ys : Vect m b}
  -> x :: xs ~=~ y :: ys
  -> x ~=~ y
vectInjective1 Refl = Refl

vectInjective2 :
  {xs : Vect n a}
  -> {ys : Vect m b}
  -> x :: xs ~=~ y :: ys
  -> xs ~=~ ys
vectInjective2 Refl = Refl

vectConcatCong:
  (xs : Vect n elem)
  -> (ys : Vect m elem)
  -> (zs : Vect m elem)
  -> (ys = zs)
  -> (xs ++ ys = xs ++ zs)
vectConcatCong xs ys ys Refl = Refl

{-
vectInjective3 :
  {xs : Vect n a}
  -> {ys : Vect m b}
  -> [x] ++ xs ~=~ [y] ++ ys
  -> [x] ~=~ [y]
vectInjective3 pf = ?rhs
-}

vectInjective4 :
  {xs : Vect n a}
  -> {ys : Vect m b}
  -> [x] ++ xs ~=~ [y] ++ ys
  -> x ~=~ y
vectInjective4 Refl = Refl

vectInjective5 :
  {xs : Vect n a}
  -> {ys : Vect m b}
  -> [x] ++ xs ~=~ [y] ++ ys
  -> xs ~=~ ys
vectInjective5 Refl = Refl




















data VectView : Vect n Nat -> Type where
  MkVectView : (xs : Vect n Nat) -> VectView xs

-- http://cattheory.com/posts/2017-11-14-scoped-implicit-conversions.html
implicit
convertVectToView : (xs : Vect n Nat) -> VectView xs
convertVectToView xs = MkVectView xs

implicit
convertViewToVect : {xs : Vect n Nat} -> VectView xs -> Vect n Nat
convertViewToVect (MkVectView xs) = xs

twoOnes : (xs : VectView [1, 1]) -> Vect 2 Nat
twoOnes xs = xs


data Ok : Nat -> Nat -> Nat -> Type where
  OkZ : Ok 0 0 0
  OkSL : (ok : Ok n m p) -> Ok (S n) m     (S p)
  OkSR : (ok : Ok n m p) -> Ok n     (S m) (S p)

inferB : 
  (a : Nat)
  -> {b : Nat}
  -> (c : Nat)
  -> {auto ok : Ok a b c}
  -> Nat
inferB {b} a c = b

data Oks : List Nat -> List Nat -> List Nat -> Type where
  OksZ : Oks [] [] []
  OksS : (ok : Ok n m p) -> Oks ns ms ps -> Oks (n :: ns) (m :: ms) (p :: ps)

--data Oks : List Type -> Type where
--  OksZ : Oks []
--  OksS : (ok : Ok a b c) -> Oks oks -> Oks $ (Ok a b c) :: oks

inferBs :
  (as : List Nat)
  -> {bs : List Nat}
  -> (cs : List Nat)
  -> {auto ok : Oks as bs cs}
  -> List Nat
inferBs {bs} as cs = bs