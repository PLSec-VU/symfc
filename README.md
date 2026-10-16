# SymFC

`SymFC` is a full-path symbolic execution engine for `GHC` Core—the internal language of `GHC`, which is based on System FC. `SymFC` is a `GHC` Core plugin, which verifies validity of a boolean statement, given an annotation, as shown below.

```haskell
{-# OPTIONS_GHC "-fplugin SymFC" #-}

module Example.Module (example) where

import SymFC (Theory (..))

{-# ANN example (Theory mempty) #-}
example :: Bool -> Bool -> SymFC.Bool
example x y = SymFC.boolean $ not x && not y == not (x || y)
```

In this case, `SymFC` shows validity of the statement, quantified over all Boolean inputs.

**NOTE**: The value supplied to `Theory` is extremely important in most real-world scenarios. An explanation can be found in section [Embeddings](#embeddings).

## Getting Started

See the [installation guide](./INSTALL.md) on how to install `SymFC` and its dependencies.

## Documentation

As of writing, this package is not hosted on `Hackage` and thus we do not host the documentation somewhere. We recommend building the documentation through haddock from your own project until we resolve this. Sorry!

## Annotation

With this, `GHC` will run `SymFC` on any expression that has an annotation with the `Theory` type, that returns an argument of type `SymFC.Bool` when saturated:

```haskell
{-# ANN expr (Theory mempty) #-}
expr :: ... -> SymFC.Bool
```

**PITFALL**: `SymFC` will only run for expressions that are in the export list of the encapsulating module. Hopefully, we can remove this quirk in the future!

`SymFC` will run when `GHC` compiles the program. If the annotated formula is not valid, `SymFC` will throw an error and display the arguments that were used to get `False` as a result.

## Built-In Types

`SymFC` support the following SMT Theories:

- Theory of Bitvectors
- Theory of Integers
- Theory of Arrays

These data types and their functions are regarded as primitives and are exported from `SymFC.BuiltIn`, along with the `Bool` primitive.

## Embeddings

SymFC directly supports computation on Algebraic Data Types. For example, we can check a function that uses `Maybe` and `Bool` as exported by `base`:

```haskell
-- NOTE: This will return a counterexample to validity when run.
{-# ANN example (Theory mempty) #-}
example :: Maybe Bool -> SymFC.Bool
example x = SymFC.boolean $ x == Just False
```

For types that are not algebraic, `SymFC` exposes an interface to interpret them as SMT solver primitives. For example, the `Int64#` type and its operation `plusInt64#` have a natural embedding with the SMT primitive `BitVec 64` and its respective addition operation. In SymFC, the user can directly encode this mapping within the annotation:

```haskell
axioms :: PluginAxioms
axioms = PluginAxioms
  { typeAxioms = fromList [(''Int64#, ''SymFC.BitVec 64)]
  , termAxioms = [('plusInt64#, 'SymFC.bvadd)]
  }

{-# ANN example (Theory axioms) #-}
example :: ... -> SymFC.Bool
```

For a reasonable mapping of `base`, check out [`sym-fc-base`](https://github.com/PLSec-VU/sym-fc-base). We also provide a mapping for `CLaSH` types and functions in [`sym-fc-clash`](https://github.com/PLSec-VU/sym-fc-clash).

```haskell
{-# ANN example (Theory SymFC.Base.axioms) #-}
example :: ... -> SymFC.Bool
```

TODO: Writing mappings is a bit more involved, we should have some separate document where we go more in depth. There are whole lot of pitfalls...
TODO: Add explanation in the sym-fc-clash and sym-fc-base repositories.
TODO: Extend explanation on PluginAxiom (at least that its a monoid and how it imports and what order).
TODO: I would actually like to move most of the explanation here into the project documentation. I think it only makes sense once we have a haddock page for it however.
