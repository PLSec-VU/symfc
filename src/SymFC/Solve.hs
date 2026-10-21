module SymFC.Solve
  ( evalWithEmbeddings
  ) where

import GHC.Clock (getMonotonicTimeNSec)
import GHC.Core qualified as GHC
import GHC.Types.Id.Make (nospecId)
import GHC.Plugins (CoreProgram, Name, Bind (..), Var)
import GHC.Utils.Outputable
  ( Outputable (..)
  , IsLine (..)
  , SDoc
  , (<+>)
  )

import Control.Monad (foldM, (>=>))

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
import Effectful.GHC.TyThing
import Effectful.GHC.TH
import Effectful.Grisette.Solver
import Effectful.Provider
import Effectful.Prim.IORef.Strict (Prim, newIORef')
import Effectful.State.Static.Local (evalState)

import Prelude hiding ((<>))

evalWithEmbeddings
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
  -> Eff es ()
evalWithEmbeddings EmbeddingsR { .. } var = provide_ @Solver do
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
  dbg @SDoc $ "SymFC evaluating '" <> ppr var <> "'..."
  start <- unsafeEff_ getMonotonicTimeNSec
  let runner = evalState global'' . evalState (WHNF.Fresh 0)
  _whnf <- runner $ WHNF.evaluate env expr
  -- TODO: We should probably check that the runner finished with a unit value!
  -- If not, something went wrong...

  end <- unsafeEff_ getMonotonicTimeNSec

  -- TODO: Ideally we can report timing outside of this debug print, maybe
  -- attached through an API call of something like 'SymFC.evaluate'?
  let time = fromIntegral (end - start) * 1e-9 :: Double
  dbg $ "*** SymFC: Elapsed time:" <+> ppr time <> "s"

  -- TODO: This API to return the counterexample doesn't work anymore. We should
  -- improve it by extending the functionality of the 'Sym' monad!
  pure ()
