module Pantomime.Passes
  ( printAndLintPass
  , checkValidityPass
  ) where

import GHC.Plugins hiding (empty, (<>), thNameToGhcName, getFirstAnnotations)
import GHC.Core.Lint
import GHC.Driver.Config.Core.Lint (initLintConfig)

import Grisette
  ( GrisetteSMTConfig (..)
  , SMTConfig (..)
  , Timing (..)
  , z3
  )

import Data.Data (Data)
import Data.Traversable (for)
import Data.Maybe (catMaybes)
import Data.ByteString.Char8 qualified as BS8
import Pantomime.Marker

import Control.Error

import Language.Haskell.TH qualified as TH

import Pantomime.Solve
import Pantomime.Unification
import Pantomime.Axiom (resolveEmbeddings)
import Pantomime.Annotation

import Effectful
import Effectful.Provider
import Effectful.Grisette.Solver
import Effectful.Exception (throwIO)
import Effectful.Context
import Effectful.Error.Static (Error, CallStack, runErrorWith)
import Effectful.Fail (Fail, runFailIO)
import Effectful.GHC.TH
import Effectful.GHC.CoreE
import Effectful.GHC.DynFlags
import Effectful.GHC.Display
import Effectful.GHC.TyThing
import Effectful.GHC.External
import Effectful.GHC.Annotations
import Effectful.GHC.Unique (HasUnique)
import Effectful.Prim.IORef.Strict (Prim, runPrim)

-- | An always non-recursive binder.
data Bind' a = Bind' a (Expr a)

-- | Transform an always non-recursive binder into a normal binder.
nonRec :: Bind' a -> Bind a
nonRec (Bind' x e) = NonRec x e

instance OutputableBndr a => Outputable (Bind' a) where
  ppr (Bind' x e) = ppr $ NonRec x e

-- | A core binder that is non-recursive.
type CoreBind' = Bind' CoreBndr

-- TODO: We should require annotations in the effect environment to do the
-- lookup for the mod guts. The pass actually only modifies the binds.
-- TODO: These passes do not modify the code. Should we make this less general
-- on the modification side? It seems to me like we should have them return a
-- unit?
-- TODO: We now support recursive functions. We should modify this function to
-- enable running them!
-- | Run the given pass on all binders that have the given annotation.
annBindsPass
  :: forall a es
   . Data a
  => HasAnnotations :> es
  => (a -> CoreBind' -> Eff es CoreBind')
  -> ModGuts
  -> Eff es ModGuts
annBindsPass pass guts = do
  -- TODO: We should probably run every annotation!
  (_, anns) <- getFirstAnnotations @a deserializeWithData guts

  binds <- for (mg_binds guts) \case
    NonRec x e | Just ann <- lookupUFM anns $ varName x -> do
      nonRec <$> pass ann (Bind' x e)
    b -> pure b

  pure guts { mg_binds = binds }

printAndLintPass
  :: forall a
   . Data a
  => CoreToDo
printAndLintPass = do
  let name = TH.nameBase 'printAndLintPass
  let pass guts = runSymbolic guts $ annBindsPass (const @_ @a printAndLint) guts
  CoreDoPluginPass name pass

-- TODO: I'm not sure if all these effects are actually used anymore. I should
-- make work of checking this at some point!
runSymbolic
  :: HasCallStack
  => ModGuts
  -> Eff
    [ Error (LookupError TH.Name)
    , Error (LookupError Name)
    , Error OversaturatedError
    , Error UnificationError
    , Error SolverError
    , Error String
    , Error SDoc
    , Prim
    , Provider_ Solver ()
    , HasAnnotations
    , THNameToGHCName
    , HasThings
    , Context Reader CoreProgram
    , Context Reader [TyCon]
    , HasUnique
    , HasInstEnvs
    , HasFamInstEnvs
    , HasExternalPackageState
    , Display
    , HasDynFlagsE
    , Fail
    , CoreE
    , IOE
    ] a
  -> CoreM a
runSymbolic guts
  = runCoreEM
  . runFailIO
  . runHasDynFlagsE
  . runDisplay
  . runHasExternalPackageState
  . runHasFamInstEnv guts
  . runHasInstEnvs guts
  . runHasUnique
  . runContextReader (mg_tcs guts)
  . runContextReader (mg_binds guts)
  . runHasThings
  . runThNameToGhcName
  . runHasAnnotations
  . runProvider_ (const $ runSolver solver)
  . runPrim
  . runErrorWith @SDoc propagateError
  . runErrorWith @String propagateErrorShow
  . runErrorWith @SolverError propagateErrorShow
  . runErrorWith @UnificationError propagateError
  . runErrorWith @OversaturatedError propagateError
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
checkValidityPass :: CoreToDo
checkValidityPass = do
  let name = TH.nameBase 'checkValidityPass
  let pass guts = runSymbolic guts $ checkValidityAndEmbed guts
  CoreDoPluginPass name pass

printAndLint
  :: HasCallStack
  => Context Reader CoreProgram :> es
  => HasDynFlagsE :> es
  => Display :> es
  => CoreBind'
  -> Eff es CoreBind'
printAndLint bind = do
  dflags <- getDynFlags
  let cfg = initLintConfig dflags []
  prog <- get @CoreProgram
  let res = lintCoreBindings' cfg prog
  debug bind
  debug res
  pure bind

checkValidityAndEmbed
  :: ( HasCallStack
     , Error String :> es
     , Error SDoc :> es
     , Error (LookupError Name) :> es
     , Error (LookupError TH.Name) :> es
     , Error SolverError :> es
     , Context Reader CoreProgram :> es
     , Context Reader [TyCon] :> es
     , Provider_ Solver () :> es
     , Prim :> es
     , HasFamInstEnvs :> es
     , HasInstEnvs :> es
     , HasThings :> es
     , HasUnique :> es
     , THNameToGHCName :> es
     , HasAnnotations :> es
     , CoreE :> es
     , IOE :> es
     )
  => ModGuts
  -> Eff es ModGuts
checkValidityAndEmbed guts = do
  (_, anns) <- getFirstAnnotations @Theory deserializeWithData guts

  markerPrimeId <- thNameToGhcName 'pantomimeMarker >>= lookupIdAll
  nothingId <- thNameToGhcName 'pantomimeNothing >>= lookupIdAll
  justId <- thNameToGhcName 'pantomimeJust >>= lookupIdAll

  (binds, results) <- fmap unzip $ for (mg_binds guts) \case
    NonRec x e | Just (Theory embeddings) <- lookupUFM anns $ varName x -> do
      embeddings' <- resolveEmbeddings embeddings
      mCounterexample <- checkValid embeddings' e
      let varNameStr = getOccString x
      case mCounterexample of
        Nothing -> do
          pure (NonRec x e, Just (varNameStr, Var nothingId))
        Just counterexample -> do
          let ceStr = showSDocUnsafe (ppr counterexample)
          ceExpr <- liftCore $ mkStringExpr ceStr
          pure (NonRec x e, Just (varNameStr, App (Var justId) ceExpr))
    b -> pure (b, Nothing)

  let results' = catMaybes results

  let resultNames = map fst results'
  case findMissingAnnotations markerPrimeId resultNames binds of
    [] -> pure ()
    (missing : _) ->
      throwIO $ PprProgramError "checkValidityPass" $
        text ("Symbolic check result not found for '" ++ missing ++ "'. Did you forget to add the {-# ANN " ++ missing ++ " (Theory ...) #-} annotation?")

  let binds' = replaceMarkerInBinds markerPrimeId results' binds
  pure guts { mg_binds = binds' }

-- | Recursively traverses all bindings in the module and replaces occurrences of
-- the 'pantomimeMarker' call with the pre-generated proof result expressions.
replaceMarkerInBinds
  :: Id
  -> [(String, CoreExpr)]
  -> [CoreBind]
  -> [CoreBind]
replaceMarkerInBinds markerPrimeId results = map goBind
  where
    goBind (NonRec b e) = NonRec b (replaceMarker markerPrimeId results e)
    goBind (Rec bs) = Rec (map (\(b, e) -> (b, replaceMarker markerPrimeId results e)) bs)

-- | Replaces any application of the 'pantomimeMarker' with its corresponding
-- compile-time Z3 proof result expression.
replaceMarker
  :: Id
  -> [(String, CoreExpr)]
  -> CoreExpr
  -> CoreExpr
replaceMarker markerPrimeId results expr = go expr
  where
    go :: CoreExpr -> CoreExpr
    go (App f a)
      | Just () <- isMarkerPrimeCall f =
          case exprToString a of
            Just assertionName ->
              case lookup assertionName results of
                Just replacementExpr -> replacementExpr
                Nothing -> App (go f) (go a)
            Nothing -> App (go f) (go a)
      | otherwise = App (go f) (go a)
            
    go (Var v) = Var v
    go (Lit l) = Lit l
    go (Lam b e) = Lam b (go e)
    go (Let (NonRec b r) e) = Let (NonRec b (go r)) (go e)
    go (Let (Rec bs) e) = Let (Rec (map (\(b, r) -> (b, go r)) bs)) (go e)
    go (Case e b t alts) = Case (go e) b t (map goAlt alts)
    go (Cast e c) = Cast (go e) c
    go (Tick t e) = Tick t (go e)
    go (Type t) = Type t
    go (Coercion c) = Coercion c

    goAlt (Alt con binders e) = Alt con binders (go e)

    isMarkerPrimeCall :: CoreExpr -> Maybe ()
    isMarkerPrimeCall (Var v) | v == markerPrimeId = Just ()
    isMarkerPrimeCall (App f' _) = isMarkerPrimeCall f'
    isMarkerPrimeCall (Cast e' _) = isMarkerPrimeCall e'
    isMarkerPrimeCall (Tick _ e') = isMarkerPrimeCall e'
    isMarkerPrimeCall _ = Nothing

-- | Rxtract a Haskell 'String' value from a GHC 'CoreExpr'
-- representing a string literal. Return Nothing if the expression is not
-- a string literal.
exprToString :: CoreExpr -> Maybe String
exprToString (Tick _ e) = exprToString e
exprToString (Cast e _) = exprToString e
exprToString (App (Var f) (Lit (LitString bs)))
  | getOccString f == "unpackCString#" || getOccString f == "unpackCStringUtf8#" =
      Just (BS8.unpack bs)
exprToString (Lit (LitString bs)) = Just (BS8.unpack bs)
exprToString _ = Nothing

-- | Scans the Core bindings for any call to 'pantomimeMarker' and returns the
-- names of all assertions that are referenced by a splice but lack the corresponding
-- 'Theory' annotation.
findMissingAnnotations
  :: Id
  -> [String]
  -> [CoreBind]
  -> [String]
findMissingAnnotations markerPrimeId resultNames binds = concatMap (goExpr . getExpr) binds
  where
    getExpr (NonRec _ e) = e
    getExpr (Rec bs) = Let (Rec bs) (Var markerPrimeId)

    goExpr :: CoreExpr -> [String]
    goExpr (App f a) =
      case isMarkerPrimeCall f of
        Just () ->
          case exprToString a of
            Just assertionName
              | assertionName `notElem` resultNames -> [assertionName]
            _ -> goExpr f ++ goExpr a
        Nothing -> goExpr f ++ goExpr a
    goExpr (Var _) = []
    goExpr (Lit _) = []
    goExpr (Lam _ e) = goExpr e
    goExpr (Let (NonRec _ r) e) = goExpr r ++ goExpr e
    goExpr (Let (Rec bs) e) = concatMap (goExpr . snd) bs ++ goExpr e
    goExpr (Case e _ _ alts) = goExpr e ++ concatMap (\(Alt _ _ body) -> goExpr body) alts
    goExpr (Cast e _) = goExpr e
    goExpr (Tick _ e) = goExpr e
    goExpr (Type _) = []
    goExpr (Coercion _) = []

    isMarkerPrimeCall :: CoreExpr -> Maybe ()
    isMarkerPrimeCall (Var v) | v == markerPrimeId = Just ()
    isMarkerPrimeCall (App f' _) = isMarkerPrimeCall f'
    isMarkerPrimeCall (Cast e' _) = isMarkerPrimeCall e'
    isMarkerPrimeCall (Tick _ e') = isMarkerPrimeCall e'
    isMarkerPrimeCall _ = Nothing
