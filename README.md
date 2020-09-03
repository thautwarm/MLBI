# Best Instantiations: The Ultimate Solution for Higher Rank Polymorphisms

Inference rules for Damas-Hindley-Milner type system are kept as-is(actually, even simpler!).

Only requires annotations for general enough higher rank types.


The inference rule for **APP**(`C` = constraints):
```
C, Gamma |- f : C', tf    Gamma, C' |- a : C'', ta
x, y: new type variablew
------------------------------
C, Gamma |- f a : [(x -> y <= tf), (x <= ta), C''], y
```

After inference, we send the constraints to a solver, which is implemented in `src/Bi.fs`.


Given
```haskell
id :: forall a. a -> a
ids :: list (forall a. a -> a)
inc :: int -> int
incs :: list (int -> int)
(:) :: forall a. a -> [a] -> [a]
```

The inference results:

```ocaml
id:ids :: [forall a. a -> a]
inc:ids :: [int -> int]
id:incs :: [int -> int]
```
