-- TODO: I guess this doesn't really need to be part of this package? Maybe it
-- should be split into a separate 'effectful-ghc' package?
module Effectful.GHC.CoreE
  ( CoreE
  , liftCore
  , runCoreE
  , runCoreEM

  , CoreReader (..)
  , CoreWriter (..)
  , getCoreReader
  , runCoreM'

  , runAllCoreE
  , runHasExternalPackageState
  , runHasThings
  , runHasDynFlagsE
  , runDisplay
  , runThNameToGhcName
  , runHasAnnotations
  , runHasUnique
  , runLoader
  ) where

import Effectful
  ( Effect
  , Dispatch (..)
  , DispatchOf
  , Eff
  , IOE
  , type (:>)
  , liftIO
  , runEff
  )
import Effectful.Dispatch.Static
  ( SideEffects (..)
  , StaticRep
  , runStaticRep
  , getStaticRep
  , putStaticRep
  )
import Effectful.Dispatch.Dynamic (interpret_)
import Effectful.GHC.External
import Effectful.GHC.TyThing
import Effectful.GHC.DynFlags
import Effectful.GHC.Display
import Effectful.GHC.Unique
import Effectful.GHC.TH (THNameToGHCName(..))
import Effectful.GHC.Annotations (HasAnnotations (..))
import Effectful.GHC.Loader (Loader (..))

import GHC.Plugins
  ( CoreM
  , HscEnv (..)
  , RuleBase
  , RuleEnv (..)
  , Module
  , NamePprCtx
  , SrcSpan
  , SimplCount
  , DumpFlag (..)
  , zeroSimplCount
  , plusSimplCount
  , addSimplCount
  , getHscEnv
  , getModule
  , getNamePprCtx
  , getSrcSpanM
  , getUniqTag
  , runCoreM
  , initRuleEnv
  , hscEPS
  , getDynFlags
  , msg
  , thNameToGhcName
  , getAnnotations
  )
import GHC.Utils.Logger (logHasDumpFlag)
import GHC.Tc.Utils.Env (lookupGlobal_maybe)
import GHC.Data.Maybe (MaybeErr(..))
import GHC.Runtime.Loader (getValueSafely)

-- | The effect that allows one to run monadic computations of type 'CoreM'.
--
-- This is an even more powerful effect than 'IOE' and it is thus not expected
-- that a user will directly carry this effect as a dependency. Instead, we
-- provide wrapper effects for operations exposed by 'CoreM'.
data CoreE :: Effect

-- | We use a static dispatch as there is only one way to implement 'CoreM' as
-- an effect.
type instance DispatchOf CoreE = Static WithSideEffects

-- | Under the hood, 'CoreM' is (almost) a Reader and Writer monad over IO.
--
-- Note that 'CoreWriter' is not a true 'Monoid'. 'mempty' is dependent on the
-- 'CoreReader' environment. As such, we implement the effect manually instead
-- of using the provided 'Reader' and 'Writer'.
data instance StaticRep CoreE = CoreE CoreReader !CoreWriter

-- | Lift a monadic operation of type 'CoreM' into the effect system.
--
-- Note, since 'CoreM' operations are run within the 'IO' monad, we explicitely
-- require the 'IOE' effect to be available. One can run already run IO
-- operations through 'CoreM', so we are explicit about requiring IO.
liftCore
  :: IOE :> es
  => CoreE :> es
  => CoreM a
  -> Eff es a
liftCore m = do
  CoreE r w1 <- getStaticRep
  (x, w2) <- liftIO $ runCoreM' r m
  let w = w1 <> w2
  putStaticRep $ CoreE r w
  pure x

-- | Run a CoreE effect.
--
-- This corresponds to running monadic 'CoreM' operations that were lifted
-- using 'liftCore'.
runCoreE
  :: IOE :> es
  => CoreReader
  -> Eff (CoreE : es) a 
  -> Eff es (a, CoreWriter)
runCoreE r eff = do
  let logger = hsc_logger . cr_hsc_env $ r
  let flag = logHasDumpFlag logger Opt_D_dump_simpl_stats
  let w = CoreWriter $ zeroSimplCount flag
  (x, CoreE _ w')<- runStaticRep (CoreE r w) eff
  pure (x, w')

-- | Run a 'CoreE' effect inside of 'CoreM'.
runCoreEM
  :: Eff '[CoreE, IOE] a
  -> CoreM a
runCoreEM eff = do
  r <- getCoreReader
  (x, simpl) <- liftIO . runEff . runCoreE r $ eff
  addSimplCount $ cw_simpl_count simpl
  pure x

-- | Duplicate of 'CoreReader' inside of 'CoreM'.
--
-- We redefine it here, as it is not exported by GHC directly.
data CoreReader = CoreReader
  { cr_hsc_env :: HscEnv
  , cr_rule_base :: RuleBase
  -- ^ Home package table rules.
  , cr_module :: Module
  , cr_name_ppr_ctx :: NamePprCtx
  , cr_loc :: SrcSpan
  -- ^ Use this for log/error messages so they are at least tagged with the
  -- right source file.
  , cr_uniq_tag :: !Char
  -- ^ Tag for creating unique values
  }

-- | Duplicate of 'CoreWriter' inside of 'CoreM'.
--
-- We redefine it here, as it is not exported by GHC directly.
newtype CoreWriter = CoreWriter
  { cw_simpl_count :: SimplCount
  -- Note: CoreWriter used to be defined with data, rather than newtype. If
  -- it is defined that way again, the cw_simpl_count field, at least, must be
  -- strict to avoid a space leak (#7702).
  }

instance Semigroup CoreWriter where
  CoreWriter lhs <> CoreWriter rhs = CoreWriter $ plusSimplCount lhs rhs

-- | Reconstruct the CoreReader from the CoreM monad.
getCoreReader :: CoreM CoreReader
getCoreReader = do
  cr_hsc_env <- getHscEnv
  -- Sadly, 'getHomeRuleBase' is not exported directly. This is a work around
  -- for now, but it is really not great...
  cr_rule_base <- re_home_rules <$> initRuleEnv undefined
  cr_module <- getModule
  cr_name_ppr_ctx <- getNamePprCtx
  cr_loc <- getSrcSpanM
  cr_uniq_tag <- getUniqTag
  pure CoreReader { .. }

-- | Same as 'runCoreM', but using records.
runCoreM' :: CoreReader -> CoreM a -> IO (a, CoreWriter)
runCoreM' CoreReader { .. } m = do
  (x, simpl) <- runCoreM
    cr_hsc_env
    cr_rule_base
    cr_uniq_tag
    cr_module
    cr_name_ppr_ctx
    cr_loc
    m
  pure (x, CoreWriter simpl)

-- | Run all sub-effects exposable by the 'CoreE' effect.
runAllCoreE
  :: IOE :> es
  => CoreE :> es
  => Eff
    ( HasUnique
    : THNameToGHCName
    : Display
    : HasThings
    : HasExternalPackageState
    : HasDynFlagsE
    : es
    ) a
  -> Eff es a
runAllCoreE
  = runHasDynFlagsE
  . runHasExternalPackageState
  . runHasThings
  . runDisplay
  . runThNameToGhcName
  . runHasUnique

-- | Run the 'ExtPackages' effect through the 'CoreE' effect.
runHasExternalPackageState
  :: IOE :> es
  => CoreE :> es
  => Eff (HasExternalPackageState : es) a
  -> Eff es a
runHasExternalPackageState = interpret_ \GetExternalPackageState -> do
  hscEnv <- liftCore getHscEnv
  liftIO $ hscEPS hscEnv

-- | Run the 'HasThings' effect through the 'CoreE' effect.
runHasThings
  :: IOE :> es
  => CoreE :> es
  => Eff (HasThings : es) a
  -> Eff es a
runHasThings = interpret_ \(LookupThing name) -> do
  env <- liftCore getHscEnv
  res <- liftIO $ lookupGlobal_maybe env name
  case res of
    Succeeded thing -> pure $ Just thing
    Failed _ -> pure Nothing

-- | Run the 'HasDynFlagsE' effect through the 'CoreE' effect.
runHasDynFlagsE
  :: IOE :> es
  => CoreE :> es
  => Eff (HasDynFlagsE : es) a
  -> Eff es a
runHasDynFlagsE = interpret_ \GetDynFlags -> do
  liftCore getDynFlags

-- | Run the 'Display' effect through the 'CoreE' effect.
runDisplay
  :: IOE :> es
  => CoreE :> es
  => Eff (Display : es) a
  -> Eff es a
runDisplay = interpret_ \(Display cls doc) -> do
  liftCore $ msg cls doc

-- | Run the 'THNameToGHCName' effect through the 'CoreE' effect.
runThNameToGhcName
  :: IOE :> es
  => CoreE :> es
  => Eff (THNameToGHCName : es) a
  -> Eff es a
runThNameToGhcName = interpret_ \(THNameToGHCName name) -> do
  liftCore $ thNameToGhcName name

-- | Run the 'HasAnnotations' effect through the 'CoreE' effect.
runHasAnnotations
  :: IOE :> es
  => CoreE :> es
  => Eff (HasAnnotations : es) a
  -> Eff es a
runHasAnnotations = interpret_ \(GetAnnotations deserialise guts) -> do
  liftCore $ getAnnotations deserialise guts

-- | Run the 'HasUnique' effect through the 'CoreE' effect.
runHasUnique
  :: IOE :> es
  => CoreE :> es
  => Eff (HasUnique : es) a
  -> Eff es a
runHasUnique = interpret_ \GetUniqueSupply -> do
  liftCore getUniqueSupplyM

-- | Run the 'Loader' effect through the 'CoreE' effect.
runLoader
  :: IOE :> es
  => CoreE :> es
  => Eff (Loader : es) a
  -> Eff es a
runLoader = interpret_ \(GetValue name ty) -> do
  env <- liftCore getHscEnv
  fmap (\(value, _, _) -> value) <$> liftIO (getValueSafely env name ty)
