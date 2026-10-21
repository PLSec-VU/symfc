module SymFC.Passes
  ( SymFC (..)
  , runSymFCPass
  , keepAnn
  ) where

import GHC.Plugins hiding (empty, (<>), thNameToGhcName, getFirstAnnotations)
import GHC.Generics (Generic)
import GHC.Tc.Types (TcM, TcGblEnv (..))
import GHC.Tc.Types.TcRef (updTcRef)

import Grisette
  ( GrisetteSMTConfig (..)
  , SMTConfig (..)
  , Timing (..)
  , z3
  )

import Control.Error

import Data.Foldable (for_)
import Data.Data (Data)

import Language.Haskell.TH qualified as TH
import Prelude hiding (break)

import SymFC.Solve
import SymFC.Unification
import SymFC.Embed (resolveEmbeddings, Embeddings)

import Effectful
import Effectful.Break (runBreak, break)
import Effectful.Provider
import Effectful.Grisette.Solver
import Effectful.Exception (throwIO)
import Effectful.Context
import Effectful.Error.Static (Error, CallStack, runErrorWith)
import Effectful.Fail (Fail, runFailIO)
import Effectful.GHC.TH
import Effectful.GHC.CoreE
import Effectful.GHC.TyThing
import Effectful.GHC.External
import Effectful.GHC.Unique (HasUnique)
import Effectful.Prim.IORef.Strict (Prim, runPrim)

-- TODO: I'm not sure if all these effects are actually used anymore. I should
-- make work of checking this at some point!
runSymbolic
  :: HasCallStack
  => ModGuts
  -> Eff
    [ Error (LookupError TH.Name)
    , Error (LookupError Name)
    , Error UnificationError
    , Error SolverError
    , Error SDoc
    , Prim
    , Provider_ Solver ()
    , THNameToGHCName
    , HasThings
    , Context Reader CoreProgram
    , Context Reader [TyCon]
    , HasUnique
    , HasInstEnvs
    , HasFamInstEnvs
    , HasExternalPackageState
    , Fail
    , CoreE
    , IOE
    ] a
  -> CoreM a
runSymbolic guts
  = runCoreEM
  . runFailIO
  . runHasExternalPackageState
  . runHasFamInstEnv guts
  . runHasInstEnvs guts
  . runHasUnique
  . runContextReader (mg_tcs guts)
  . runContextReader (mg_binds guts)
  . runHasThings
  . runThNameToGhcName
  . runProvider_ (const $ runSolver solver)
  . runPrim
  . runErrorWith @SDoc propagateError
  . runErrorWith @SolverError propagateErrorShow
  . runErrorWith @UnificationError propagateError
  . runErrorWith @(LookupError Name) propagateError
  . runErrorWith @(LookupError TH.Name) propagateErrorShow
  where
    -- TODO: We could let the user decide which solver no?
    solver = z3
      { sbvConfig = (sbvConfig z3)
        { verbose = True
        , timing = PrintTiming
        }
      }

    panicDocIO :: String -> SDoc -> Eff es a
    panicDocIO s doc = throwIO $ PprPanic s doc

    propagateError
      :: Outputable o
      => CallStack
      -> o
      -> Eff es a
    propagateError cs doc = panicDocIO "runSymbolic" $ vcat
      [ ppr doc
      , prettyCallStackDoc cs
      ]

    propagateErrorShow
      :: Show s
      => CallStack
      -> s
      -> Eff es a
    propagateErrorShow cs = propagateError cs . text @SDoc . show

-- TODO: Instead of just running a pass per binder, I want to accumulate the
-- results for all checks. In fact, this isn't even a pass as we do not modify
-- the CoreExpr. This is also true for the other 'passes' in this module.
-- TODO: I think the name on this function should be different. It is not really
-- indicative what it checks now. Or at least, the annotation it specialises to.
runSymFCPass :: CoreToDo
runSymFCPass = do
  let name = TH.nameBase 'runSymFC
  let pass guts = runSymbolic guts $ runSymFC guts
  CoreDoPluginPass name pass

-- | Call the 'SymFC' plugin on this function.
--
-- A function with this annotation is expected to have type @Sym ()@.
newtype SymFC where
  SymFC :: Embeddings -> SymFC
  deriving (Show, Data, Generic)

-- | The main pass that runs the symbolic evaluator.
runSymFC
  :: HasCallStack
  => Error SDoc :> es
  => Error (LookupError Name) :> es
  => Error (LookupError TH.Name) :> es
  => Error SolverError :> es
  => Context Reader CoreProgram :> es
  => Context Reader [TyCon] :> es
  => Prim :> es
  => HasInstEnvs :> es
  => HasFamInstEnvs :> es
  => HasThings :> es
  => HasUnique :> es
  => THNameToGHCName :> es
  => Provider_ Solver () :> es
  => ModGuts
  -> Eff es ModGuts
runSymFC guts = do
  for_ (mg_anns guts) \(Annotation target value) -> runBreak do
    -- Early return with unused value.
    let break' = break ()

    -- Fetch the embeddings of this annotation, if any.
    let valueM = fromSerialized @SymFC deserializeWithData value
    SymFC embeddings <- maybe break' pure valueM

    -- Fetch the identifier this corresponds to.
    name <- case target of
      NamedTarget name -> pure name
      ModuleTarget _ -> break'
    idn <- lookupIdLocal name

    -- TODO: Validate the type of 'idn'?

    -- Run the evaluator for the identifier.
    embeddings' <- resolveEmbeddings embeddings
    evalWithEmbeddings embeddings' idn
    -- TODO: I think perhaps the best thing to do is to pass in the 'SymFC' a
    -- list of template haskell names indexed by an integer. A primitive
    -- operation can index this list to emit a counterexample to it. We can
    -- use a writer monad to track these. I wonder if emitting the tag or the
    -- resolved name directly makes more sense? For the latter we need an
    -- extra effect to do the lookup. I feel like just emitting the number is
    -- fine?
  pure guts

-- | A pass that ensures every definition with a 'SymFC' annotation is kept
-- alive for the main plugin to run.
keepAnn
  :: [CommandLineOption]
  -> ModSummary
  -> TcGblEnv
  -> TcM TcGblEnv
keepAnn _opt _summary tcg = do
  for_ (tcg_anns tcg) \(Annotation target value) -> if
    | Just _ <- fromSerialized @SymFC deserializeWithData value
    , NamedTarget name <- target -> do
      updTcRef (tcg_keep tcg) $ flip extendNameSet name
    | otherwise -> pure ()
  pure tcg
