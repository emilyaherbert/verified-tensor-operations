
## a + b = c

Our last meeting we discussed using a proof that shows that you can infer `b` from `a` and `c`, where `a + b = c`:

```
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
```

Then that can be implemented for a List of Nats, which allows you to infer `b = [b_0, ..., b_n]` from `a = [a_0, ..., a_n]` and `c = [c_0, ..., c_n]` where `a_i + b_i = c_i`:

```
data Oks : List Nat -> List Nat -> List Nat -> Type where
  OksZ : Oks [] [] []
  OksS : (ok : Ok n m p) -> Oks ns ms ps -> Oks (n :: ns) (m :: ms) (p :: ps)

inferBs :
  (as : List Nat)
  -> {bs : List Nat}
  -> (cs : List Nat)
  -> {auto ok : Oks as bs cs}
  -> List Nat
inferBs {bs} as cs = bs
```

## tindex

`Oks` got me closer to implementing the multi-dimension index (`tindex`) method that I was focusing on and shed light the actual underlying issue. Basically, I don't think what I am trying to do is possible in the current version of Idris. In order to write a typesafe version of tindex where the user can call it with just the indices and tensor (i.e. `tindex [4,6] foo`), the type signature of `tindex` has to extract some portion of the dimensions of `foo`. The core issue of why this version of `tindex` fails is that Idris is not able to perform this extraction.

`(::)` is a constructor that injects information about the type of the dimensions into the type of the tensor. The `(::)` in `Tensor (n :: dims) ty` tells Idris that at the most immediate level the dimensions of the tensor will be constructed with `(::)`. Using `(++)` inside of `tindex` is not as helpful, as `(++)` is a function and is applied directly, rather than as a means of relaying type information. Basically, when you attempt to partition the dimensions into `cs ++ dims`, Idris doesn't understand that you are trying to find `cs` from `cs ++ dims` and instead thinks that you are trying to create some `dims'` using `cs ++ dims`. `tindex` subsequently thinks `cs` is an implicit argument, which means everything blows up when you try to infer `bs` because Idris is now inferring both `bs` and `cs`:

```
tindex : 
  (as : Dims (S n))
  -> {bs : Dims (S n)}
  -> Tensor (cs ++ dims) ty
  -> {auto ok : Oks as bs cs}
  -> Tensor dims ty
```

## using a (++) constructor

So, the first thought solution to this is to create a `(++)` constructor so that you can use `(++)` like you do `(::)`:

```
data Dims : Nat -> Type where
  Nil : Dims 0
  (::) : (x : Nat) -> (xs : Dims n) -> Dims (S n)
  (++) : (xs : Dims n) -> (xs' : Dims m) -> Dims (n + m)
```

This could work, except for the fact that you need some type of implicit equivalency/ automatic conversion between instances of `Dims n` constructed with `(::)` and instances of `Dims n` constructed with `(++)`. You would need the `(::)` constructor to be able to match both `(::)` and `(++)`. As far as I can tell, there is no way to implement this currently, although there is a blurb on implementing copatterns which would make this straightforward (https://github.com/idris-lang/Idris-dev/wiki/Copatterns).


## Hacky solution

As I was typing this, I think I thought of an alternate solution that is hacky but might work. Instead of asking Idris for equivalency between the `(::)` and `(++)` constructors, just implement Dims as:

```
data Dims : Nat -> Type where
  Nil : Dims 0
  (++) : (xs : Vect n Nat) -> (ys : Dims m) -> Dims (n + m)
```

This would allow you to intuitively use `(++)` in `tindex`, with the caveat being you have to use `[n] ++ dims` where you would have otherwise used `n :: dims`. I'll have to think about this more and try it out at some point.