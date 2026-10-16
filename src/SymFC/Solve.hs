module SymFC.Solve
  ( checkValid
  ) where

import GHC.Clock (getMonotonicTimeNSec)
import GHC.Core qualified as GHC
import GHC.Types.Id.Make (nospecId)
import GHC.Plugins (CoreProgram, Name, Bind (..), Var)
import GHC.Utils.Outputable
  ( Outputable (..)
  , IsLine (..)
  , SDoc
  , text
  , (<+>)
  )

import Grisette (LogicalOp (..), Union, onUnion)

import Control.DeepSeq (NFData (..))
import Control.Monad (foldM, (>=>))
import Control.Monad.Except (runExceptT)

import Data.Traversable (for)
import Language.Haskell.TH qualified as TH

import SymFC.BuiltIn qualified as Builtin
import SymFC.Util (dbg)
import SymFC.Embed (EmbeddingsR (..))
import SymFC.WHNF qualified as WHNF

import Effectful
import Effectful.Context
import Effectful.Dispatch.Static (unsafeEff_)
import Effectful.Error.Static
import Effectful.Exception (evaluate)
import Effectful.GHC.TyThing
import Effectful.GHC.TH
import Effectful.Grisette.Solver
import Effectful.Provider
import Effectful.Prim.IORef.Strict (Prim, newIORef')
import Effectful.State.Static.Local (evalState)

import Prelude hiding ((<>))

checkValid
  :: forall es
   . HasCallStack
  => Error SDoc :> es
  => Error (LookupError TH.Name) :> es
  => Error (LookupError Name) :> es
  => Error SolverError :> es
  => Context Reader CoreProgram :> es
  => Prim :> es
  => HasThings :> es
  => THNameToGHCName :> es
  => Provider_ Solver () :> es
  => EmbeddingsR
  -> Var
  -> Eff es (Maybe SDoc)
checkValid EmbeddingsR { .. } var = do
  let lookupIdTH = thNameToGhcName >=> lookupId

  -- Add the primitive bindings to the global environment.
  primitives <- WHNF.primitives
  let global = WHNF.extendMany WHNF.emptyEnv primitives

  -- Add the term embeddings to the global environment.
  terms <- for termEmbeddingsR \(idn, expr) -> do
    thunk <- newIORef' $ WHNF.Thunk WHNF.emptyEnv expr
    pure (idn, thunk)
  let global' = WHNF.extendMany global terms

  -- Add in binder for 'nospec'. Sadly, this one is not exposed by, so we cannot
  -- write this as an embedding.
  identity <- lookupIdTH 'id
  global'' <- WHNF.extendBind global' $ NonRec nospecId (GHC.Var identity)

  -- Create the local substitution environment.
  program <- get @CoreProgram
  env <- foldM WHNF.extendBind WHNF.emptyEnv program

  -- Construct the final expression, which uses a helper to run the monad.
  runSymId <- lookupIdTH 'Builtin.runSym
  let expr = GHC.App (GHC.Var runSymId) (GHC.Var var)

  -- Force the thunk. We measure the timing of the evaluator also.
  start <- unsafeEff_ getMonotonicTimeNSec
  let runner = evalState global'' . evalState (WHNF.Fresh 0)
  whnf <- runner $ WHNF.evaluate env expr

  let whnf' = whnf >>= \case
        WHNF.Lit (WHNF.Bool value) -> pure value
        _ -> WHNF.mkUndefinedBehaviour

  let isValid = onUnion @Union \case
        Left WHNF.Unreachable -> true
        Left WHNF.UndefinedBehaviour -> false
        Left WHNF.Raise {} -> false
        Right value -> value

  let eq = isValid $ runExceptT whnf'

  evaluate $ rnf eq
  end <- unsafeEff_ getMonotonicTimeNSec

  solution <- provide_ @Solver $ solve (symNot eq)

  -- TODO: Ideally we can report timing outside of this debug print, maybe
  -- attached through an API call of something like 'SymFC.evaluate'?
  let time = fromIntegral (end - start) * 1e-9 :: Double
  dbg $ "*** SymFC: Elapsed time:" <+> ppr time <> "s"

  -- TODO: This API to return the counterexample doesn't work anymore. We should
  -- improve it by extending the functionality of the 'Sym' monad!
  pure case solution of
    Satisfiable model -> Just $ hcat
      [ "TODO: Add in API to instantiate a 'SymFC.fresh' value with a model."
      , text (show model)
      ]
    Unsatisfiable -> Nothing
    Unknown -> Just "Solver returned 'unknown'..."
