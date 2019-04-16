module Tensor

import Data.Vect
import Data.HVect
import Dimension

%access public export
%default total

data Tensor : Dims n -> Type -> Type where
  TZ : (x : ty) -> Tensor [] ty
  TS : (xs : Vect n (Tensor dims ty)) -> Tensor (n :: dims) ty

Scalar : Type -> Type
Scalar ty = Tensor [] ty

get_dims : {dims : Dims n} -> Tensor dims a -> Dims n
get_dims {dims} _ = dims

--------------------------------------------------------------------------------
-- Building
--------------------------------------------------------------------------------

fill : ty -> (dims : Dims n) -> Tensor dims ty
fill v [] = TZ v
fill v (x :: xs) = TS $ replicate x $ fill v xs

fillLike : ty1 -> Tensor dims ty2 -> Tensor dims ty1
fillLike v xs = fill v $ get_dims xs

--------------------------------------------------------------------------------
-- Interfaces
--------------------------------------------------------------------------------

Eq ty => Eq (Tensor dims ty) where
  (==) (TZ x) (TZ y) = x == y
  (==) (TS xs) (TS ys) = foldl (\acc,elem => acc && elem) True $ zipWith (\x,y => x == y) xs ys

Functor (Tensor dims) where
  map func (TZ x) = TZ $ func x
  map func (TS xs) = TS $ map (map func) xs

||| Depth first.
Foldable (Tensor dims) where
  foldr func acc (TZ x) = func x acc
  foldr func acc (TS xs@((TZ y) :: ys)) = foldr (\(TZ e),a => func e a) acc xs
  foldr func acc (TS xs) = foldr (\e,a => foldr func a e) acc xs

  foldl func acc (TZ x) = func acc x
  foldl func acc (TS xs@((TZ y) :: ys)) = foldl (\a,(TZ e) => func a e) acc xs
  foldl func acc (TS xs) = foldl (\a,e => foldl func a e) acc xs

||| Combines a collection of a collections by folding on subcollections, then combining results.
interface Aggregatable (t : Type -> Type) where
  aggregater : (elem -> acc -> acc) -> (acc -> acc -> acc) -> acc -> t elem -> acc
  aggregatel : (acc -> elem -> acc) -> (acc -> acc -> acc) -> acc -> t elem -> acc

||| Breadth first.
Aggregatable (Tensor dims) where
  aggregater seqOp combOp acc (TZ x) = seqOp x acc
  aggregater seqOp combOp acc (TS xs@((TZ y) :: ys)) = foldr (\(TZ e),a => seqOp e a) acc xs
  aggregater seqOp combOp acc (TS xs) = foldr (\e,a => combOp e a) acc $ map (aggregater seqOp combOp acc) xs

  aggregatel seqOp combOp acc (TZ x) = seqOp acc x
  aggregatel seqOp combOp acc (TS xs@((TZ y) :: ys)) = foldl (\a,(TZ e) => seqOp a e) acc xs
  aggregatel seqOp combOp acc (TS xs) = foldl (\a,e => combOp a e) acc $ map (aggregatel seqOp combOp acc) xs

--------------------------------------------------------------------------------
-- DecEq
--------------------------------------------------------------------------------

-- TODO

--------------------------------------------------------------------------------
-- Zips and unzips
--------------------------------------------------------------------------------

zipWith :
  (a -> b -> c)
  -> Tensor dims a
  -> Tensor dims b
  -> Tensor dims c
zipWith f (TZ x)  (TZ y)  = TZ $ f x y
zipWith f (TS xs) (TS ys) = TS $ Data.Vect.zipWith (Tensor.zipWith f) xs ys

zipWith3 :
  (a -> b -> c -> d)
  -> Tensor dims a
  -> Tensor dims b
  -> Tensor dims c
  -> Tensor dims d
zipWith3 f (TZ x)  (TZ y)  (TZ z)  = TZ $ f x y z
zipWith3 f (TS xs) (TS ys) (TS zs) = TS $ Data.Vect.zipWith3 (Tensor.zipWith3 f) xs ys zs

zip :
  Tensor dims a
  -> Tensor dims b
  -> Tensor dims (a, b)
zip xs ys = Tensor.zipWith (\x,y => (x,y)) xs ys

zip3 :
  Tensor dims a
  -> Tensor dims b
  -> Tensor dims c
  -> Tensor dims (a, b ,c)
zip3 xs ys zs = Tensor.zipWith3 (\x,y,z => (x,y,z)) xs ys zs

unzip : 
  Tensor dims (a, b)
  -> (Tensor dims a, Tensor dims b)
unzip (TZ (x, y)) = (TZ x, TZ y)
unzip (TS xs) =
  let recur = map (Tensor.unzip) xs in
  let (ys, zs) = Data.Vect.unzip recur in
  (TS ys, TS zs)

unzip3 : 
  Tensor dims (a, b, c)
  -> (Tensor dims a, Tensor dims b, Tensor dims c)
unzip3 (TZ (x, y, z)) = (TZ x, TZ y, TZ z)
unzip3 (TS xs) =
  let recur = map (Tensor.unzip3) xs in
  let (ys, zs, zzs) = Data.Vect.unzip3 recur in
  (TS ys, TS zs, TS zzs)

--------------------------------------------------------------------------------
-- Combine-two
--------------------------------------------------------------------------------

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

concat : Tensor (n :: dims) ty -> Tensor (m :: dims) ty -> Tensor (n + m :: dims) ty
concat (TS xs) (TS ys) = TS $ xs ++ ys

(++) : Tensor (n :: dims) ty -> Tensor (m :: dims) ty -> Tensor (n + m :: dims) ty
(++) xs ys = concat xs ys

--------------------------------------------------------------------------------
-- Indexing
--------------------------------------------------------------------------------

||| Data.Vect.index without using a Fin.
vectIndex :
  (n : Nat)
  -> Vect (n + (S m)) ty
  -> ty
vectIndex Z     (x :: xs) = x
vectIndex (S k) (x :: xs) = vectIndex k xs

index :
  (n : Nat)
  -> Tensor ((n + (S m)) :: dims) ty
  -> Tensor dims ty
index n (TS xs) = vectIndex n xs

{-
tIndex :
  Fin n
  -> Fin m
  -> Tensor (n :: m :: dims) ty
  -> Tensor dims ty
tIndex i j xs = Tensor.index j $ Tensor.index i xs
-}

{-
tIndex :
  {dims : Dims n}
  -> HVect (map (\x => Fin x) (m :: dims))
  -> Tensor (m :: dims) ty
  -> Tensor dims ty
-}

{-
tIndex :
  Tensor dims ty
  -> HVect (map (\x => Fin x) dims)
  -> Tensor dims ty
tIndex xs is = xs
-}

--------------------------------------------------------------------------------
-- Slicing
--------------------------------------------------------------------------------

||| Get the first n elements of the first dimension of a Tensor.
take :
  (n : Nat)
  -> Tensor ((n + m) :: dims) ty
  -> Tensor (n :: dims) ty
take n (TS xs) = TS $ Data.Vect.take n xs

||| Drop the first n elements of the first dimension of a Tensor.
drop :
  (n : Nat)
  -> Tensor ((n + m) :: dims) ty
  -> Tensor (m :: dims) ty
drop n (TS xs) = TS $ Data.Vect.drop n xs

||| Get the first n elements of the first dimension of a Tensor.
||| Equivalent of take.
takeLeft :
  (n : Nat)
  -> Tensor ((n + m) :: dims) ty
  -> Tensor (n :: dims) ty
takeLeft n xs = take n xs

||| Get the last n elements of the first dimension of a Tensor.
takeRight :
  (n : Nat)
  -> Tensor ((m + n) :: dims) ty
  -> Tensor (n :: dims) ty
takeRight {m} n xs = drop m xs

||| Drop the first n elements of the first dimension of a Tensor.
||| Equivalent of drop.
dropLeft :
  (n : Nat)
  -> Tensor ((n + m) :: dims) ty
  -> Tensor (m :: dims) ty
dropLeft n xs = drop n xs

||| Drop the last n elements of the first dimension of a Tensor.
dropRight :
  (n : Nat)
  -> Tensor ((m + n) :: dims) ty
  -> Tensor (m :: dims) ty
dropRight {m} n xs = take m xs

slice :
  (start : Nat)
  -> (count : Nat)
  -> Tensor (start + (count + m) :: dims) ty
  -> Tensor (count :: dims) ty
slice start count xs = Tensor.take count $ Tensor.drop start xs

--------------------------------------------------------------------------------
-- Reshapes
--------------------------------------------------------------------------------

flatten :
  Tensor (n :: m :: dims) ty
  -> Tensor (n * m :: dims) ty
flatten (TS []) = TS []
flatten (TS (x :: xs)) = concat x $ flatten (TS xs)

squeeze :
  Tensor (1 :: dims) ty
  -> Tensor dims ty
squeeze (TS (x :: [])) = x

squeezeAt :
  (n : Nat)
  -> {front : Dims n}
  -> {back : Dims (S m)}
  -> Tensor (front ++ (1 :: back)) ty
  -> Tensor (front ++ back) ty

unsqueeze :
  Tensor dims ty
  -> Tensor (1 :: dims) ty
unsqueeze (TZ x) = TS [TZ x]
unsqueeze (TS xs) = TS [TS xs]

--------------------------------------------------------------------------------
-- Updating values
--------------------------------------------------------------------------------

||| Data.Vect.replaceAt without using a Fin.
vectReplaceAt :
  (n : Nat)
  -> ty
  -> Vect (n + (S m)) ty
  -> Vect (n + (S m)) ty
vectReplaceAt Z     v (x :: xs) = v :: xs
vectReplaceAt (S k) v (x :: xs) = x :: (vectReplaceAt k v xs)

replaceAt :
  (n : Nat)
  -> Tensor dims ty
  -> Tensor ((n + (S m)) :: dims) ty
  -> Tensor ((n + (S m)) :: dims) ty
replaceAt n v (TS xs) = TS $ vectReplaceAt n v xs

||| Data.Vect.updateAt without using a Fin.
vectUpdateAt :
  (n : Nat)
  -> (ty -> ty)
  -> Vect (n + (S m)) ty
  -> Vect (n + (S m)) ty
vectUpdateAt Z     f (x :: xs) = (f x) :: xs
vectUpdateAt (S k) f (x :: xs) = x :: (vectUpdateAt k f xs)

updateAt :
  (n : Nat)
  -> (Tensor dims ty -> Tensor dims ty)
  -> Tensor ((n + (S m)) :: dims) ty
  -> Tensor ((n + (S m)) :: dims) ty
updateAt n f (TS xs) = TS $ vectUpdateAt n f xs

--------------------------------------------------------------------------------
-- Properties
--------------------------------------------------------------------------------

min : Ord ty => ty -> Tensor dims ty -> ty
min acc xs = foldl (\a,e => if a < e then a else e) acc xs

max : Ord ty => ty -> Tensor dims ty -> ty
max acc xs = foldl (\a,e => if a > e then a else e) acc xs

-- TODO: squeeze + unsqueeze = original
-- TODO: unsqueeze + squeeze = original

||| Unsqueeze then squeeze does nothing.
squeezeUnsqueezed :
  (xs : Tensor dims ty)
  -> Tensor.squeeze (Tensor.unsqueeze xs) = xs
squeezeUnsqueezed (TZ x) = Refl
squeezeUnsqueezed (TS xs) = Refl

||| Squeeze then unsqueeze does nothing.
unsqueezeSqueezed :
  (xs : Tensor (1 :: dims) ty)
  -> Tensor.unsqueeze (Tensor.squeeze xs) = xs
unsqueezeSqueezed (TS xs) = ?rhs_1

--------------------------------------------------------------------------------
-- Test tensors
--------------------------------------------------------------------------------

test1 : Tensor [10, 10] Double
test1 = Tensor.fill 0.5 [10, 10]

test2 : Tensor [10, 10] Double
test2 = Tensor.fill 1.5 [10, 10]

test3 : Tensor [10, 10, 10] Double
test3 = Tensor.fill 1.0 [10, 10, 10]

test4 : Tensor [4, 3, 4, 3] Double
test4 = Tensor.fill 1.0 [4, 3, 4, 3]

test5 : Tensor [1, 3, 4, 3] Double
test5 = Tensor.fill 1.0 [1, 3, 4, 3]

--------------------------------------------------------------------------------
-- Tested functions
--------------------------------------------------------------------------------

||| Tensor [10, 10, 10] Double -> Tensor [10, 10] Double
index_ : Tensor [10, 10] Double
index_ = Tensor.index 4 test3

slice_ : Tensor [3, 10, 10] Double
slice_ = Tensor.slice 3 3 test3

flatten_ : Tensor [100, 10] Double
flatten_ = Tensor.flatten test3

squeeze_ : Tensor [3, 4, 3] Double
squeeze_ = Tensor.squeeze test5

--squeezeAt_ : Tensor [3, 4, 3] Double
--squeezeAt_ = Tensor.squeezeAt 0 test5

unsqueeze_ : Tensor [1, 1, 3, 4, 3] Double
unsqueeze_ = Tensor.unsqueeze test5

replaceAt_ : Tensor [10, 10, 10] Double
replaceAt_ = Tensor.replaceAt 9 test1 test3

updateAt_ : Tensor [10, 10] Double
updateAt_ = Tensor.updateAt 9 (\x => x + x) test1