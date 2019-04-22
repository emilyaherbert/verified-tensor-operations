module Utility

data Vect : (n : Nat) -> (ty : Type) -> Type where
  Nil : Vect 0 ty
  (::) : (x : ty) -> (xs : Vect n ty) -> Vect (S n) ty
  --(++) : (xs : Vect n ty) -> (ys : Vect m ty) -> Vect (n + m) ty

(++) :
  Vect n ty
  -> Vect m ty
  -> Vect (n + m) ty
(++) [] [] = []
(++) 

{-

headUnequal : DecEq a =>
  {xs : Vect n a}
  -> {ys : Vect n a}
  -> (contra : (x = y) -> Void)
  -> (x :: xs) = (y :: ys)
  -> Void
headUnequal contra Refl = contra Refl

tailUnequal : DecEq a =>
  {xs : Vect n a}
  -> {ys : Vect n a}
  -> (contra : (xs = ys) -> Void)
  -> (x :: xs) = (y :: ys)
  -> Void
tailUnequal contra Refl = contra Refl

headUnequal2 : DecEq a =>
  {xs : Vect n a}
  -> {ys : Vect n a}
  -> (contra : (x = y) -> Void)
  -> (x ++ xs) = (y ++ ys)
  -> Void
headUnequal2 contra Refl = contra Refl

tailUnequal2 : DecEq a =>
  {xs : Vect n a}
  -> {ys : Vect n a}
  -> (contra : (xs = ys) -> Void)
  -> (x ++ xs) = (y ++ ys)
  -> Void
tailUnequal2 contra Refl = contra Refl

DecEq a => DecEq (Vect n a) where
  decEq [] [] = Yes Refl
  decEq (x :: xs) (y :: ys) = case decEq x y of
                                No contra => No (headUnequal contra)
                                Yes Refl => case decEq xs ys of
                                                Yes Refl => Yes Refl
                                                No contra => No (tailUnequal contra)
  decEq (x ++ xs) (y ++ ys) = case decEq x y of
                                No contra => No (headUnequal2 contra)
                                Yes Refl => case decEq xs ys of
                                                Yes Refl => Yes Refl
                                                No contra => No (tailUnequal2 contra)
-}

Dims : Nat -> Type
Dims n = Vect n Nat

data Tensor : Dims n -> Type -> Type where
  TZ : (x : ty) -> Tensor [] ty
  TS : (xs : Vect n (Tensor dims ty)) -> Tensor (n :: dims) ty
  TC : (xs : Vect n (Tensor dims ty)) -> Tensor ([n] ++ dims) ty
  -- TS : (xs : Vect n (Tensor dims ty)) -> (ys : Vect m (Tensor dims ty))-> Tensor (n + m :: dims) ty

test1 : Tensor [10, 10] Double
test1 = TS [TS [TZ 0.5, TZ 0.5, TZ 0.5, TZ 0.5, TZ 0.5, TZ 0.5, TZ 0.5, TZ 0.5, TZ 0.5, TZ 0.5],
            TS [TZ 0.5, TZ 0.5, TZ 0.5, TZ 0.5, TZ 0.5, TZ 0.5, TZ 0.5, TZ 0.5, TZ 0.5, TZ 0.5],
            TS [TZ 0.5, TZ 0.5, TZ 0.5, TZ 0.5, TZ 0.5, TZ 0.5, TZ 0.5, TZ 0.5, TZ 0.5, TZ 0.5],
            TS [TZ 0.5, TZ 0.5, TZ 0.5, TZ 0.5, TZ 0.5, TZ 0.5, TZ 0.5, TZ 0.5, TZ 0.5, TZ 0.5],
            TS [TZ 0.5, TZ 0.5, TZ 0.5, TZ 0.5, TZ 0.5, TZ 0.5, TZ 0.5, TZ 0.5, TZ 0.5, TZ 0.5],
            TS [TZ 0.5, TZ 0.5, TZ 0.5, TZ 0.5, TZ 0.5, TZ 0.5, TZ 0.5, TZ 0.5, TZ 0.5, TZ 0.5],
            TS [TZ 0.5, TZ 0.5, TZ 0.5, TZ 0.5, TZ 0.5, TZ 0.5, TZ 0.5, TZ 0.5, TZ 0.5, TZ 0.5],
            TS [TZ 0.5, TZ 0.5, TZ 0.5, TZ 0.5, TZ 0.5, TZ 0.5, TZ 0.5, TZ 0.5, TZ 0.5, TZ 0.5],
            TS [TZ 0.5, TZ 0.5, TZ 0.5, TZ 0.5, TZ 0.5, TZ 0.5, TZ 0.5, TZ 0.5, TZ 0.5, TZ 0.5],
            TS [TZ 0.5, TZ 0.5, TZ 0.5, TZ 0.5, TZ 0.5, TZ 0.5, TZ 0.5, TZ 0.5, TZ 0.5, TZ 0.5]]