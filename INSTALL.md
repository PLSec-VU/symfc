# `SymFC` Installation Guide

This document describes the external dependencies of `SymFC`, how to add the `sym-fc` package as a dependency to your project and how to enable the compiler plugin.

## SMT Solver

`SymFC` assumes that the [`Z3`](https://github.com/z3prover/z3) SMT solver is installed and available from your `PATH`. To see if an installation is available on your machine, run the following command:

```sh
z3 --version
```

In the future, we aim to make it configurable which solver is used.

## Stack or Cabal build

This guide explains how to use either [`Stack`](https://docs.haskellstack.org/en/stable/) or [`Cabal`](https://www.haskell.org/cabal/) to build `SymFC`. If you don't already have either of these installed yet, we recommend managing them through [`GHCup`](https://www.haskell.org/ghcup/). Throughout the guide, we will also have collapsed fields like the ones below that help you with commands for your respective build tool of choise:

<details>
<summary><code>Stack</code> setup</summary>

In case you want to set up a new project, you can do so by running `stack new`. To build the project at any stage, run `stack build`.
</details>

<details>
<summary><code>Cabal</code> setup</summary>

TODO
</details>

During this guide, feel free to build your project after any adjustment to the configuration files to see if they are still consistent.

## Example Repository

If you are simply looking to try out `SymFC`, or want to start a fresh project with `SymFC`, you may also use the [example repository](https://github.com/PLSec-VU/sym-fc-example) as a template. It can also serve as a reference to inspect in case you get stuck. If the guide was unclear in any way (or you have other suggestions), do [let us know](https://github.com/PLSec-VU/sym-fc/issues/new) so we can improve it!

## GHC Version

`SymFC` is a `GHC` compiler plugin, which causes it to heavily rely on the API that `GHC` exposes to its users. At the time of writing, `SymFC` is built using `GHC` version `9.12.2`. Altough untested, it is likely that `SymFC` is incompatible with other versions of `GHC`.

<details>
<summary><code>Stack</code> setup</summary>

In the project's `stack.yaml` file, ensure the `snapshot` (or deprecated `resolver`) field is set to a snapshot that uses the correct `GHC` version. One can pick a snapshot from [`Stackage`](https://www.stackage.org/snapshots).

```yaml
snapshot: <snapshot-version>
```

We recommend using a long term support (LTS) version, though one does not yet exist for this `GHC` version at the time of writing.

Alternatively, you can select a `GHC` version without a curated set of compatible packages. This might require more setup later configuring the `extra-deps` field of your `stack.yaml` file.

```yaml
snapshot: ghc-9.12.2
```
</details>

<details>
<summary><code>Cabal</code> setup</summary>

TODO
</details>

We aim to make `SymFC` compatible with a wider range of `GHC` versions in
the future!

## Grisette

`SymFC` uses a custom version of [`Grisette`](https://hackage-content.haskell.org/package/grisette-0.13.0.1), which can be found [here](https://github.com/RobinWebbers/grisette). In the future, we hope the [pull request](https://github.com/lsrcz/grisette/pull/309) for the extension will get merged and pushed to hackage. Sadly, this is one of the blocking factors for `SymFC` to get pushed as a package on [`Hackage`](https://hackage.haskell.org/).

<details>
<summary><code>Stack</code> setup</summary>

Add grisette to the `extra-deps` of your `stack.yaml` file:

```yaml
extra-deps:
- git: https://github.com:RobinWebbers/grisette.git
  commit: ae4d837886efb2e7838f89271f343d6fa8130388
```

You may add the `extra-deps` field if it does not already exist.
</details>

<details>
<summary><code>Cabal</code> setup</summary>

TODO
</details>

## SymFC

We can now add a dependency to `SymFC` in your project. Additionally, we will add a dependency to [`sym-fc-base`](https://github.com/PLSec-VU/sym-fc-base). It is not important to understand what this contains for the purpose of this setup, but feel free to check it out if you're interested.

<details>
<summary><code>Stack</code> setup</summary>

Add the `sym-fc` and `sym-fc-base` packages to the `extra-deps` field of your `stack.yaml` file. This lets stack know which version of these packages to build with, should they be used. For now, `SymFC` is not available on [`Hackage`](https://hackage.haskell.org/) so we'll have to specify the git repository and which commit hash to use instead. We recommend getting the latest commit from the `main` branch of the respective repositories.

```yaml
extra-deps:
- git: https://github.com/PLSec-VU/sym-fc.git
  commit: <commit-hash-sym-fc>
- git: https://github.com/PLSec-VU/sym-fc-base.git
  commit: <commit-hash-sym-fc-base>
```

Additionally, you will need to add these dependencies to a stanza (e.g. `library`, `executables`) of your choise. This exposes `SymFC` modules to be available to import in your project. The following shows how to add the dependencies to your `library` build:

```yaml
library:
  dependencies:
  - sym-fc
  - sym-fc-base
```

At this point, you can build the project using `stack build` to see if the `snapshot` you picked in one of the [previous steps](#ghc-version) works for the build. Though unusual, `Stack` may refuse to build if the set of packages was not consistent with themselves. You can try different snapshots until you find one that works.

If you decided to build without a curated `snapshot` (i.e. you provided just the compiler version), then you have to manually add dependencies to `extra-deps`. `Stack` will make suggestions when you build: these are generally good but could lead to inconsistencies. How to fully resolve these inconsistencies is sadly out of the scope of this guide.
</details>

<details>
<summary><code>Cabal</code> setup</summary>

TODO
</details>

## Enable Plugin

To allow `SymFC` to run on your code examples, its plugin needs to be enabled during compilation. You may either enable it per module or project wide. To enable `SymFC` in a single module, add the following pragma at the top of the respective file.

```haskell
{-# OPTIONS_GHC "-fplugin SymFC" #-}

module Example.Module where
```

You can enable it project wide by passing this same option in your build files.

<details>
<summary><code>Stack</code> setup</summary>

To illustrate, here we enable `SymFC` when building your project's library.

```yaml
library:
  ghc-options:
  - -fplugin SymFC
```
</details>

<details>
<summary><code>Cabal</code> setup</summary>

TODO
</details>

## Try it!

At this point, the project should compile with the `SymFC` plugin. You can
try to build the following example module.

```haskell
{-# OPTIONS_GHC "-fplugin SymFC" #-} -- or use system-wide setup

module Example (example) where

import SymFC (Theory (..))
import qualified SymFC.BuiltIn as SymFC
import qualified SymFC.Base as Base

{-# ANN example (Theory Base.axioms) #-}
example :: Int -> SymFC.Bool
example x = SymFC.boolean $ x + x == 2 * x
```

If all went well, you should see a query to an SMT solver pop up in your terminal during compilation. `SymFC` should tell you that the stub is indeed valid.

**NOTE**: As of writing, `SymFC` only verifies a function if it is exported in the module. Make sure this is true in case you do not see any result.

## Documentation

This concludes the setup guide. Sadly, I cannot refer you to a `Hackage` page with documentation as it is not up yet. The [project page](https://github.com/PLSec-VU/sym-fc) contains more information on `SymFC`. You may also want to build the documentation through [`Haddock`](https://haskell-haddock.readthedocs.io/latest/).
