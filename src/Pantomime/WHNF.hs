{-# LANGUAGE MagicHash #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE BangPatterns #-}

module Pantomime.WHNF
  ( WHNF
  , Bottom
  , mkBottom
  , mkUnreachable
  , mkUndefinedBehaviour

  , force
  , evaluate

  , Env
  , emptyEnv
  , lookup
  , extend
  , extendMany
  , extendBind

  , With (..)

  , Thunks
  , emptyThunks

  , CollectThunks (..)
  , collectThunks
  ) where

import Control.Arrow ((>>>))
import Control.Monad (join, unless, (>=>))
import Control.Monad.Cont (ContT)
import Control.Monad.Trans (MonadTrans (lift))
import Control.Monad.Except (ExceptT (..))
import Control.Monad.Except qualified as Except
import Data.Bits (Bits (..))
import Data.Coerce (coerce)
import Data.Composition ((.:))
import Data.Constraint (Dict (..), HasDict (evidence))
import Data.Data (Proxy (..))
import Data.Foldable (traverse_, for_)
import Data.Function (on)
import Data.HashMap.Strict (HashMap)
import Data.HashMap.Strict qualified as HashMap
import Data.List (sortBy)
import Data.Traversable (for)
import Data.Typeable (type (:~:) (Refl), eqT)
import Effectful (Eff, type (:>))
import Effectful.Dispatch.Static (unsafeEff_)
import Effectful.Error.Static (Error, HasCallStack, throwError_)
import Effectful.GHC.TH (THNameToGHCName, thNameToGhcName)
import Effectful.GHC.TyThing (HasThings, LookupError, lookupId, lookupDataCon)
import Effectful.Prim.IORef.Strict
  ( Prim
  , IORef'
  , readIORef'
  , writeIORef'
  , newIORef'
  )
import Effectful.Reader.Static (ask, Reader)
import Effectful.State.Static.Local (State, get, put, execState)
import GHC.Core qualified as GHC
import GHC.Data.Maybe (whenIsJust, runMaybeT, MaybeT (MaybeT))
import GHC.Generics (Generic (..))
import GHC.Plugins
  ( CoreExpr
  , CoreBndr
  , DataCon
  , Id
  , IdEnv
  , CoreAlt
  , CoreBind
  , TyCon
  , IsLine ((<>))
  , Arity
  , Name
  , NonDetUniqFM (NonDetUniqFM)
  , lookupVarEnv
  , emptyVarEnv
  , isId
  , unitDataCon
  , extendVarEnv
  , dataConTagZ
  , dataConTyCon
  , isEnumerationTyCon
  , unitTyCon
  )
import GHC.Plugins qualified as GHC
import GHC.IO (unsafePerformIO)
import GHC.IsList (IsList (..))
import GHC.StableName (StableName, makeStableName)
import GHC.TypeLits (SomeNat (..), someNatVal, natVal)
import GHC.TypeNats (withSomeSNat, pattern SNat)
import GHC.Utils.Outputable
  ( SDoc
  , Outputable (..)
  , IsLine ((<+>), text, sep)
  , IsDoc (vcat)
  , hang
  , parens
  )
import Grisette
  ( SymBool
  , SymInteger
  , SymIntN
  , Union
  , Default (..)
  , MergingStrategy (..)
  , Mergeable (..)
  , SimpleMergeable (..)
  , SymEq ((.==), (./=))
  , SymOrd (..)
  , LogicalOp (symNot, symImplies)
  , SymFromIntegral (symFromIntegral)
  , BitCast (..)
  , SExpr (NumberAtom)
  , SignConversion (..)
  , SymShift (..)
  , Identifier (..)
  , wrapStrategy
  , product2Strategy
  , merge
  , sym
  , simple
  , symNot
  , (.&&)
  , (.||)
  )
import Grisette qualified
import Language.Haskell.TH qualified as TH
import Pantomime.BuiltIn qualified as Builtin
import Pantomime.Grisette.Mergeable (impossible)
import Pantomime.Literal (Literal (..), SomeLiteralType (..), LiteralType (..))
import Pantomime.PrimOp (PrimOp (..), PrimOps)
import Pantomime.PrimOp qualified as PrimOp
import Pantomime.Orphan.GHC ()
import Pantomime.Orphan.Grisette (pattern Single, pattern If)
import Pantomime.Tsil
import Pantomime.Util
  ( SymBitVec
  , SomeBitVec (..)
  , KnownPos
  , foldlBy
  , failWith
  , posNat
  , withExit
  )
import Prelude hiding ((<>), lookup)

type WHNF = WHNF' 'Shared

type WHNF' shr = Runtime (Value shr)

instance Outputable (WHNF' shr) where
  ppr = pprRuntime ppr

data Value shr where
  Lit :: !Literal -> Value shr
  Opr :: !PrimOp -> !Arity -> !(Tsil (Arg shr)) -> Value shr
  Con :: !(Constructor shr) -> Value shr
  Lam :: !Env -> !Id -> !CoreExpr -> Value shr
  deriving Generic

instance Outputable (Value shr) where
  ppr = \case
    Lit lit -> ppr lit
    Opr op _ args -> hang (ppr op) 2 $ sep ("<thunk>" <$ toList args)
    Con con -> ppr con
    Lam _closure bndr body -> ppr $ GHC.Lam bndr body

instance Mergeable (Value 'Mergeable) where
  rootStrategy = SortedStrategy @Int
    (\case
      Lit {} -> 0
      Opr {} -> 1
      Con {} -> 2
      Lam {} -> 3)
    \case
      0 -> wrapStrategy
        rootStrategy
        Lit
        \case Lit lit -> lit ; _ -> impossible
      1 -> product2Strategy
        (uncurry Opr)
        (\case Opr op arity args -> ((op, arity), args) ; _ -> impossible)
        rootStrategy
        NoStrategy
      2 -> wrapStrategy
        rootStrategy
        Con
        \case Con con -> con ; _ -> impossible
      3 -> NoStrategy
      _ -> impossible

-- | Share the arguments of data constructors and primitive operations.
--
-- By 'share', we mean to wrap the merged arguments (i.e. those in a 'Union') in
-- 'IORef' so that evaluation is shared between occurrences.
share :: Prim :> es => WHNF' 'Mergeable -> Eff es WHNF
share = do
  -- Share branches through 'IORef'.
  let go = \case
        Single thunk -> pure thunk
        If guard true false -> do
          true' <- go true
          false' <- go false
          newIORef' $ Ite guard true' false'

  -- Ensure the value is merged and then wrap thunks.
  merge >>> traverse \case
    Lit lit -> pure $ Lit lit
    Opr op arity args -> do
      args' <- for args go
      pure $ Opr op arity args'
    Lam closure bndr body -> pure $ Lam closure bndr body
    Con con -> case con of
      EnumCon tag tc -> pure $ Con (EnumCon tag tc)
      DataCon dc args -> do
        args' <- for args go
        pure $ Con (DataCon dc args')

-- | Put the WHNF value into a mergeable state.
--
-- This wraps any arguments into a 'Union', such that they are compatible with
-- the merging. The wrinkle this solves is that a 'Thunk' cannot have an
-- instance of 'SimpleMergeable' because it needs to create a fresh 'IORef'.
-- Hence, we allow merging by first using a 'Union' to wrap the any 'Thunk'.
mergeable :: WHNF -> WHNF' 'Mergeable
mergeable = fmap \case
  Lit lit -> Lit lit
  Opr op arity args -> Opr op arity $ fmap Single args
  Lam closure bndr body -> Lam closure bndr body
  Con con -> case con of
    EnumCon tag tc -> Con (EnumCon tag tc)
    DataCon dc args -> do
      let args' = Single <$> args
      Con (DataCon dc args')

data Constructor shr where
  DataCon :: !DataCon -> !(Tsil (Arg shr)) -> Constructor shr
  EnumCon :: !(SymBitVec 64) -> !TyCon -> Constructor shr

instance Outputable (Constructor shr) where
  ppr = \case
    DataCon dc args -> hang (ppr dc) 2 $ sep ("<thunk>" <$ toList args)
    -- TODO: This tag print is bad, should give it an 'Outputable' instance.
    EnumCon tag tc -> "tagToEnum#" <+> ppr tc <+> text (show tag)

instance Mergeable (Constructor 'Mergeable) where
  rootStrategy = SortedStrategy
    (\case
      DataCon {} -> True
      EnumCon {} -> False)
    \case
      True -> product2Strategy
        DataCon
        (\case DataCon dc args -> (dc, args) ; _ -> impossible)
        rootStrategy
        NoStrategy
      False -> wrapStrategy
        rootStrategy
        (uncurry EnumCon)
        \case EnumCon tag tc -> (tag, tc) ; _ -> impossible

-- | We use a 'Union' to accumulate 'Thunks' as they cannot be merged in a pure
-- setting.
--
-- TODO: It is probably better to implement a merging algorithm for WHNF, as it
-- is literally the only thing we will be merging anyway. This will safe us a
-- lot of allocations... It's more work though, so I'll do it later!
--
-- Later note: we are also merging 'Alt'. Still, I think in this case we should
-- have a merging function that allows one to construct an 'IORef''. I wonder if
-- this is unsafe? Reading and writing is obviously bad, but we don't need this
-- when merging.
type family Arg (stage :: Sharing) where
  Arg 'Mergeable = Union Thunk
  Arg 'Shared = Thunk

data Sharing where
  Mergeable :: Sharing
  Shared :: Sharing

type Runtime = ExceptT Bottom Union

data Bottom where
  Diverge :: Bottom
  Unreachable :: Bottom
  UndefinedBehaviour :: Bottom
  -- TODO: Not sure what we want to do with raise regarding merging.
  Raise :: !(Value 'Mergeable) -> Bottom
  deriving Generic
  deriving Mergeable via Default Bottom

instance Outputable Bottom where
  ppr = \case
    Diverge -> "⊥"
    Unreachable -> "∅"
    UndefinedBehaviour -> "?"
    Raise expr -> "raise#" <+> ppr expr

mkBottom :: Bottom -> Runtime a
mkBottom = Except.throwError

mkUnreachable :: Runtime a
mkUnreachable = mkBottom Unreachable

mkUndefinedBehaviour :: Runtime a
mkUndefinedBehaviour = mkBottom UndefinedBehaviour

-- TODO: Regarding CAF. If the CAF has a side-effect (which is not supported
-- ATM), we should probably only consider this side-effect during the execution
-- path in which the CAF was actually forced no? I think CAF+side-effect is
-- pretty nosy, so we should be considerate of this once we allow for global
-- side-effects during symbolic evaluation. Note that I do think we should add
-- this eventually...
--
-- Actually, it's not just CAF's that are a problem for side-effects in
-- pure code. In other places, we then also need to track when the value was
-- forced... In my head, this seems as though we would create a branch with the
-- path condition and leave the else unforced. I guess we should only do this
-- if we actually have some side-effect though no? I.e. maybe the 'evaluate'
-- function can tell us whether we triggered a side-effect in pure code and then
-- we can act accordingly in 'force'?

-- | Global environment for binders.
--
-- This environment initially should contain the term embeddings required for
-- the evaluation of a definition. During evaluation, any variable that has an
-- unfolding (and is not already in the global environment) is added. This is to
-- support CAF (Constant Applicative Form), which ensures that Haskell forces
-- top-level expressions only once.
type Global = Env

newtype Env where
  Env :: IdEnv Thunk -> Env

instance Outputable Env where
  ppr (Env env) = ppr $ fmap (const @SDoc "<thunk>") env

emptyEnv :: Env
emptyEnv = Env emptyVarEnv

lookup :: Env -> Id -> Maybe Thunk
lookup = coerce $ lookupVarEnv @Thunk

extend :: Env -> Id -> Thunk -> Env
extend = coerce $ extendVarEnv @Thunk

extendMany :: Foldable f => Env -> f (Id, Thunk) -> Env
extendMany = foldl' $ uncurry . extend

-- | Extend an environment with thunks for the given binder.
extendBind
  :: Prim :> es
  => Env
  -> CoreBind
  -> Eff es Env
extendBind env = \case
  GHC.NonRec bndr body -> do
    thunk <- newIORef' $ Thunk env body
    pure $ extend env bndr thunk
  GHC.Rec pairs -> do
    rec
      pairs' <- for pairs \(bndr, rhs) -> do
        -- NOTE: We need to pass in the new environment with all binders
        -- present. We use the fixpoint computation for this purpose.
        thunk <- newIORef' $ Thunk env' rhs
        pure (bndr, thunk)
      env' <- pure $ extendMany env pairs'
    pure env'

-- | A value that may or may not have been forced.
--
-- Thunks should share computation, which we achieve through an 'IORef''.
type Thunk = IORef' ThunkKind

-- | The type of thunks we support.
--
-- Either a thunk has already been forced, it is a closure or it is a symbolic
-- branch of two thunks.
data ThunkKind where
  -- | An already forced value.
  WHNF :: !WHNF -> ThunkKind
  -- | An unforced closure.
  Thunk :: !Env -> !CoreExpr -> ThunkKind
  -- | A symbolic branch of two thunks.
  Ite :: SymBool -> Thunk -> Thunk -> ThunkKind

instance Outputable ThunkKind where
  ppr = \case
    WHNF whnf -> ppr whnf
    Thunk env expr -> hang "CLOSURE:" 2 $ sep [ppr env, ppr expr]
    Ite guard _ _ -> hang "ite" 2 $ sep [text (show guard), "<thunk>", "<thunk>"]

-- | Force a thunk to weak-head normal form.
force
  :: HasCallStack
  => Error (LookupError Name) :> es
  => Error (LookupError TH.Name) :> es
  => Error SDoc :> es
  => HasThings :> es
  => Prim :> es
  => Reader PrimOps :> es
  => State Global :> es
  => THNameToGHCName :> es
  => Thunk
  -> Eff es WHNF
force thunk = do
  whnf' <- force' thunk
  share whnf'

-- TODO: Callstack growth
-- | Force a thunk to weak-head normal form and keeps it mergeable.
force'
  :: HasCallStack
  => Error (LookupError Name) :> es
  => Error (LookupError TH.Name) :> es
  => Error SDoc :> es
  => HasThings :> es
  => Prim :> es
  => Reader PrimOps :> es
  => State Global :> es
  => THNameToGHCName :> es
  => Thunk
  -> Eff es (WHNF' 'Mergeable)
force' thunk = do
  kind <- readIORef' thunk
  case kind of
    WHNF whnf -> pure $ mergeable whnf
    Thunk env expr -> do
      whnf <- evaluate env expr
      writeIORef' thunk $ WHNF whnf
      pure $ mergeable whnf
    Ite guard true false -> do
      true' <- force' true
      false' <- force' false
      pure $ mrgIte guard true' false'

-- TODO: Fix callstack growth.
-- | Evaluate the given closure.
evaluate
  :: HasCallStack
  => Error (LookupError Name) :> es
  => Error (LookupError TH.Name) :> es
  => Error SDoc :> es
  => HasThings :> es
  => Prim :> es
  => Reader PrimOps :> es
  => State Global :> es
  => THNameToGHCName :> es
  => Env
  -> CoreExpr
  -> Eff es WHNF
evaluate @es env = \case
  GHC.Var var -> withExit \exit -> do
    -- Early return helper functions.
    let exitJust :: Maybe a -> (a -> Eff es WHNF) -> ContT WHNF (Eff es) ()
        exitJust cond body = whenIsJust cond $ \inner -> do
          result <- lift $ body inner
          exit result

    -- Lookup as a local variable.
    exitJust (lookup env var) force

    -- Lookup as a global variable.
    global <- lift $ get @Global
    exitJust (lookup global var) force

    -- Try to resolve the variable through an unfolding. We additionally extend
    -- the global environment if we succeeded.
    let lookupUnfolding = GHC.maybeUnfoldingTemplate . GHC.realIdUnfolding
    exitJust (lookupUnfolding var) \body -> do
      thunk <- newIORef' $ Thunk env body
      put $ extend global var thunk
      force thunk

    -- Wrap a data constructor. Note that we first attempt the global
    -- environment lookup to allow for embeddings on data constructors.
    exitJust (GHC.isDataConId_maybe var) \dc -> do
      let tc = dataConTyCon dc
      let con = case isEnumerationTyCon tc of
            True -> EnumCon (fromIntegral $ dataConTagZ dc) tc
            False -> DataCon dc Lin
      pure $ pure (Con con)

    -- TODO: I think I could remove the reliance on the 'PrimOps' by simply
    -- adding the operation to the global environment.
    -- Lookup as a primitive.
    prims <- lift $ ask @PrimOps
    exitJust (PrimOp.lookup prims var) \op -> do
      primitive op (PrimOp.arity op) Lin

    -- No more ways to resolve, so we return an error.
    let err = "Could not resolve global variable '" <> ppr var <> "'"
    lift $ throwError_ @SDoc err
  GHC.Lit lit -> do
    -- Get the literal and its conversion function.
    (lit', convert, _) <- literal lit
    convert' <- thNameToGhcName >=> lookupId $ convert

    -- Force the conversion function and thunk the argument.
    fun <- evaluate emptyEnv $ GHC.Var convert'
    arg <- newIORef' $ WHNF (pure $ Lit lit')

    -- Apply the conversion function to the literal.
    apply fun arg
  GHC.Lam bndr body
    -- Create a function value.
    | isId bndr -> pure $ pure (Lam env bndr body)
    -- The variable is not computationally relevant, so we elide the function.
    | otherwise -> evaluate env body
  GHC.App fun arg
    | GHC.isValArg arg -> do
      -- Evaluate the function.
      fun' <- evaluate env fun

      -- We create a new reference once before evaluating the many possible
      -- function calls so we can share the result accross these.
      arg' <- newIORef' $ Thunk env arg

      -- Apply the argument to the function.
      apply fun' arg'
    -- We elide the application for non computationally relevant arguments.
    | otherwise -> evaluate env fun
  GHC.Let bind body -> do
    env' <- extendBind env bind
    evaluate env' body
  GHC.Case scrut bndr _ty alts -> do
    -- First we force the scrutinee.
    scrut' <- evaluate env scrut

    -- Split the default pattern, if any.
    let (alts', def) = GHC.findDefault alts

    -- We start by grouping values that take the same path. This way, we will
    -- only evaluate the right-hand-side of each alternative at most once.
    let grouped = merge do
          value <- scrut'
          lift $ match value alts'

    -- Evaluate the grouped alternatives.
    unmerged <- for grouped $ branch env bndr def

    -- Join the branches and make them shareable.
    share $ join unmerged
  GHC.Cast body _ -> evaluate env body
  GHC.Coercion _ -> pure $ pure coercion
  GHC.Type _ -> throwError_ @SDoc "Cannot evaluate a type."
  GHC.Tick _ body -> evaluate env body

-- | Like evaluate, but leaves the expression in a mergeable state.
evaluate'
  :: HasCallStack
  => Error (LookupError Name) :> es
  => Error (LookupError TH.Name) :> es
  => Error SDoc :> es
  => HasThings :> es
  => Prim :> es
  => Reader PrimOps :> es
  => State Global :> es
  => THNameToGHCName :> es
  => Env
  -> CoreExpr
  -> Eff es (WHNF' 'Mergeable)
evaluate' env expr = mergeable <$> evaluate env expr

-- TODO: Coercions are I think represented as unboxed units in the runtime.
-- For now, I'll just return a unit constructor. We can see if this needs to
-- change at some point.
coercion :: Value shr
coercion = do
  let tag = fromIntegral $ dataConTagZ unitDataCon
  Con (EnumCon tag unitTyCon)

-- | Apply the function to the argument.
apply
  :: HasCallStack
  => Error (LookupError Name) :> es
  => Error (LookupError TH.Name) :> es
  => Error SDoc :> es
  => HasThings :> es
  => Prim :> es
  => Reader PrimOps :> es
  => State Global :> es
  => THNameToGHCName :> es
  => WHNF
  -> Thunk
  -> Eff es WHNF
apply fun arg = do
  -- For every lambda, we extend the environment with the argument and evaluate
  -- the body.
  unmerged <- for fun \case
    Lam env' bndr body -> do
      let env'' = extend env' bndr arg
      evaluate' env'' body
    Con (DataCon dc args) -> do
      let args' = Snoc args arg
      let whnf = pure $ Con (DataCon dc args')
      pure $ mergeable whnf
    Opr op arity args -> do
      whnf <- primitive op (arity - 1) $ Snoc args arg
      pure $ mergeable whnf
    _ -> pure mkUndefinedBehaviour
  share $ join unmerged

-- | A branch during evaluation.
--
-- This data structure is used to merge branches that end up evaluating the
-- right hand side. Specifically, this means we want to merge all expressions
-- the would end up matching the default pattern. As it is valid
data Alt where
  -- | Branch for a matching data constructor.
  DataAlt :: DataCon -> [(CoreBndr, Thunk)] -> CoreExpr -> Alt
  -- | Default branch: no matching pattern.
  --
  -- This is the main purpose for the existince of this data structure: to
  -- merge multipe non-matching branches. This way, we only need to evaluate
  -- the right-hand side *once* with this merged value.
  DEFAULT :: WHNF' 'Mergeable -> Alt
  -- | Triggered whenever type confusion happened and no alternative could be
  -- selected.
  --
  -- This could be due to existential types or (broken) unsafe code.
  None :: Alt

instance Outputable Alt where
  ppr = \case
    DataAlt dc args rhs -> ppr dc <+> ppr (fst <$> args) <+> ppr rhs
    DEFAULT scrut -> "DEFAULT:" <+> ppr scrut
    None -> "None"

instance Mergeable Alt where
  rootStrategy = SortedStrategy
    (\case
      DataAlt dc _ _ -> Left dc
      DEFAULT _ -> Right True
      None -> Right False)
    \case
      -- NOTE: The only reason why we keep these unmerged is that we actually
      -- expect there to be only a single DataAlt for each constructor anyway.
      -- That is, they are already merged. The 'Alt' data type only exists to
      -- merge default branches before evaluation of the branch.
      Left _ -> NoStrategy
      Right True -> SimpleStrategy \cases
        guard (DEFAULT true) (DEFAULT false) -> do
          DEFAULT $ mrgIte guard true false
        _ _ _ -> impossible
      Right False -> SimpleStrategy \_ true _ -> true

-- | Match a value to possibly many alternatives.
--
-- The goal of these alternatives is group values that take the same path. This
-- way, we will only evaluate the right-hand-side of each alternative at most
-- once.
--
-- WARNING: The given alternatives are expected to be stripped from the default
-- case.
match :: Value 'Shared -> [CoreAlt] -> Union Alt
match value alts = do
  let def = pure $ DEFAULT (mergeable $ pure value)
  foldlBy def alts \acc (GHC.Alt ac bndrs rhs) -> case (value, ac) of
    -- Match a enumeration constructor to a DataCon if they originate from the
    -- same TyCon.
    (Con (EnumCon tag tc), GHC.DataAlt dc) | tc == dataConTyCon dc -> do
      -- Get the tag of the data constructor and create the branch
      -- condition.
      let tag' = fromIntegral $ dataConTagZ dc
      let guard = tag .== tag'

      -- Construct the alternative and create the branch.
      let alt = pure $ DataAlt dc [] rhs
      mrgIte guard alt acc

    -- Match the data constructor.
    (Con (DataCon dc args), GHC.DataAlt dc')
      -- If they match exactly, we return just the alternative.
      | dc == dc' -> do
        let bndrs' = zip (filter isId bndrs) $ toList args
        pure $ DataAlt dc bndrs' rhs
      -- They don't match exactly, but we are matching the correct type so we
      -- return the accumulator.
      | dataConTyCon dc == dataConTyCon dc' -> acc

    -- TODO: Add match on literal here!

    -- If no match, this should result in undefined behaviour for all
    -- branches: the type does not match, so even default cannot match.
    _ -> pure None

-- | Evaluate an alternative.
branch
  :: HasCallStack
  => Error (LookupError Name) :> es
  => Error (LookupError TH.Name) :> es
  => Error SDoc :> es
  => HasThings :> es
  => Prim :> es
  => Reader PrimOps :> es
  => State Global :> es
  => THNameToGHCName :> es
  => Env
  -- ^ The current variables in scope.
  -> CoreBndr
  -- ^ The case binder.
  -> Maybe CoreExpr
  -- ^ Default branch, if available.
  -> Alt
  -- ^ The alternative to evaluate.
  -> Eff es (WHNF' 'Mergeable)
branch env bndr def = \case
  -- Evaluate the data constructor alternative.
  DataAlt dc bndrs rhs -> do
    let tc = dataConTyCon dc
    let scrut' = pure $ Con case isEnumerationTyCon tc of
          True -> EnumCon (fromIntegral $ dataConTagZ dc) tc
          False -> DataCon dc $ fromList (snd <$> bndrs)
    thunk <- newIORef' $ WHNF scrut'
    let env' = extendMany env $ (bndr, thunk) : bndrs
    evaluate' env' rhs

  -- Evaluate the default alternative, if there is a default case exists.
  DEFAULT scrut' | Just rhs <- def -> do
    scrut'' <- share scrut'
    thunk <- newIORef' $ WHNF scrut''
    let env' = extend env bndr thunk
    evaluate' env' rhs

  -- No match, so we get 'UndefinedBehaviour' for this branch.
  _ -> pure mkUndefinedBehaviour

-- | Convert a literal into a information preserving representation in the
-- symbolic evaluator.
--
-- Additionally, this returns the corresponding function 'Id' to convert this
-- literal into the original primitive and en 'Id' for an equality function.
--
-- Both functions require an embedding to be used.
literal
  :: HasCallStack
  => Error SDoc :> es
  => GHC.Literal
  -> Eff es (Literal, TH.Name, TH.Name)
literal = \case
  GHC.LitNumber ty num -> do
    (size, convert, eq) <- case ty of
      -- TODO: The bitvector size should be related to the platform size.
      GHC.LitNumInt -> pure (64, 'Builtin.toInt#, 'Builtin.eqInt#)
      GHC.LitNumInt8 -> pure (8, 'Builtin.toInt8#, 'Builtin.eqInt8#)
      GHC.LitNumInt16 -> pure (16, 'Builtin.toInt16#, 'Builtin.eqInt16#)
      GHC.LitNumInt32 -> pure (32, 'Builtin.toInt32#, 'Builtin.eqInt32#)
      GHC.LitNumInt64 -> pure (64, 'Builtin.toInt64#, 'Builtin.eqInt64#)
      GHC.LitNumWord -> pure (64, 'Builtin.toWord#, 'Builtin.eqWord#)
      GHC.LitNumWord8 -> pure (8, 'Builtin.toWord8#, 'Builtin.eqWord8#)
      GHC.LitNumWord16 -> pure (16, 'Builtin.toWord16#, 'Builtin.eqWord16#)
      GHC.LitNumWord32 -> pure (32, 'Builtin.toWord32#, 'Builtin.eqWord32#)
      GHC.LitNumWord64 -> pure (64, 'Builtin.toWord64#, 'Builtin.eqWord64#)
      GHC.LitNumBigNat -> throwError_ @SDoc "TODO: support ByteArray# literal"

    lit' <- withSomeSNat size \(SNat @n) -> do
      -- TODO: This cannot fail. I guess this might not be the nicest way to
      -- do this... Ideally we construct a KnownNat already in its definition.
      Dict <- failWith @SDoc "Nat should be positive" $ posNat @n
      pure $ BitVec @n (fromInteger num)
    pure (lit', convert, eq)
  lit -> throwError_ @SDoc $ "Unsupported literal '" <> ppr lit <> "'"

-- | Build a primitive.
--
-- If the primitive is not saturated, we evaluate it. Otherwise, we return the
-- primitive as is.
primitive
  :: HasCallStack
  => Error (LookupError Name) :> es
  => Error (LookupError TH.Name) :> es
  => Error SDoc :> es
  => HasThings :> es
  => Prim :> es
  => Reader PrimOps :> es
  => State Global :> es
  => THNameToGHCName :> es
  => PrimOp
  -> Arity
  -> Tsil Thunk
  -> Eff es WHNF
primitive op arity args = case arity of
  0 -> primitive' op $ toList args
  _ -> do
    let whnf = pure $ Opr op arity args
    pure whnf

primitive'
  :: forall es
   . HasCallStack
  => Error (LookupError Name) :> es
  => Error (LookupError TH.Name) :> es
  => Error SDoc :> es
  => HasThings :> es
  => Prim :> es
  => Reader PrimOps :> es
  => State Global :> es
  => THNameToGHCName :> es
  => PrimOp
  -> [Thunk]
  -> Eff es WHNF
primitive' = \case
  IteOp -> PBool :-> PAny :-> PAny :-> RS PAny ## \guardR true false -> do
    share $ guardR >>= \guard -> on (mrgIte guard) mergeable true false
  -- TagToEnumOp :: PrimOp
  -- DataToTagOp :: PrimOp
  -- RaiseOp :: PrimOp
  -- UnsafeEqualityProofOp :: PrimOp

  -- Symbolic variable operations.
  SymbolicPrimOp -> PPrimTy :-> PInteger :-> RS PAny ## \primR idnR -> do
    -- Join the 'Runtime' monads of both arguments.
    let argsR = liftA2 (,) primR idnR
    for argsR \(prim, idn) -> do
      -- Get the type of the symbolic value and get evidence that indeed this
      -- type is supported.
      SomeLiteralType ty <- pure prim
      Dict <- pure $ evidence ty

      -- Extract a concrete identifier.
      idn' <- case idn of
        Grisette.Con idn' -> pure idn'
        _ -> throwError_ @SDoc "symbolicP expect concrete identifier"

      -- Construct a symbolic variable
      let var = sym . simple $ Identifier "x" (NumberAtom idn')

      -- Return the size bitvector.
      pure $ Lit (Literal ty var)

  -- Boolean operations.
  TrueOp -> RS PBool ## pure (pure Grisette.true)
  FalseOp -> RS PBool ## pure (pure Grisette.false)
  NotOp -> unary PBool ## pure . fmap symNot
  ImpliesOp -> binary PBool ## pure .: liftA2 symImplies
  AndOp -> binary PBool ## pure .: liftA2 (.&&)
  OrOp -> binary PBool ## pure .: liftA2 (.||)
  IffOp -> binary PBool ## pure .: liftA2 (.||)
  XorOp -> binary PBool ## pure .: liftA2 (./=)

  -- Integer operations.
  IntToBitVecOp -> PInteger :-> PInteger :-> RS PBitVec ## \sizeR valueR -> do
    -- Join the 'Runtime' monads of both arguments.
    let argsR = liftA2 (,) sizeR valueR
    for argsR \(size, value) -> do
      -- Extract a concrete size.
      -- TODO: I guess we could support a cascading 'if then else' of concrete
      -- values? This might happen in some code involving existentials. Same for
      -- 'symbolicP' btw.
      size' <- case size of
        Grisette.Con size' -> pure size'
        _ -> throwError_ @SDoc "i2bv expects a concrete size"

      -- Ensure that it is a positive number.
      let err = "i2bv expects a positive size"
      SomeNat @n _ <- failWith @SDoc err $ someNatVal size'
      Dict <- failWith @SDoc err $ posNat @n

      -- Return the size bitvector.
      pure $ SomeBitVec @n (symFromIntegral value)
  IntNegOp -> unary PInteger ## pure . fmap negate
  IntAbsOp -> unary PInteger ## pure . fmap abs
  IntAddOp -> binary PInteger ## pure .: liftA2 (+)
  IntMulOp -> binary PInteger ## pure .: liftA2 (*)
  IntDivOp -> binary PInteger ## pure .: liftA2 div
  IntModOp -> binary PInteger ## pure .: liftA2 mod
  IntEqOp -> cmp PInteger ## pure .: liftA2 (.==)
  IntNeqOp -> cmp PInteger ## pure .: liftA2 (./=)
  IntLeOp -> cmp PInteger ## pure .: liftA2 (.<=)
  IntLtOp -> cmp PInteger ## pure .: liftA2 (.<)

  -- Bitvector operations.
  BitVecUToIntOp -> PBitVec :-> RS PInteger ## do
    pure . fmap \(SomeBitVec bv) -> symFromIntegral bv
  BitVecSToIntOp -> PBitVec :-> RS PInteger ## do
    pure . fmap \(SomeBitVec @n bv) -> do
      symFromIntegral $ bitCast @_ @(SymIntN n) bv
  BitVecSizeOp -> PBitVec :-> RS PInteger ## do
    pure . fmap \(SomeBitVec @n _) -> fromInteger $ natVal @n Proxy
  BitVecNotOp -> unary PBitVec ## pure . bvunary complement
  BitVecNegOp -> unary PBitVec ## pure . bvunary negate
  BitVecAndOp -> binary PBitVec ## pure .: bvbinary (.&.)
  BitVecOrOp -> binary PBitVec ## pure .: bvbinary (.|.)
  BitVecXorOp -> binary PBitVec ## pure .: bvbinary xor
  BitVecAddOp -> binary PBitVec ## pure .: bvbinary (+)
  BitVecMulOp -> binary PBitVec ## pure .: bvbinary (*)
  BitVecUDivOp -> binary PBitVec ## pure .: bvbinary div
  BitVecSDivOp -> binary PBitVec ## pure .: bvbinary (sbinary div)
  BitVecURemOp -> binary PBitVec ## pure .: bvbinary rem
  BitVecSRemOp -> binary PBitVec ## pure .: bvbinary (sbinary rem)
  BitVecShl -> binary PBitVec ## pure .: bvbinary symShift
  BitVecLShr -> binary PBitVec ## pure .: bvbinary symShiftNegated
  BitVecAShr -> binary PBitVec ## pure .: bvbinary (sbinary symShiftNegated)
  BitVecEqOp -> cmp PBitVec ## pure .: bvcompare (.==)
  BitVecNeqOp -> cmp PBitVec ## pure .: bvcompare (./=)
  BitVecULeOp -> cmp PBitVec ## pure .: bvcompare (.<=)
  BitVecSLeOp -> cmp PBitVec ## pure .: bvcompare (scompare (.<=))
  BitVecULtOp -> cmp PBitVec ## pure .: bvcompare (.<)
  BitVecSLtOp -> cmp PBitVec ## pure .: bvcompare (scompare (.<))
  -- BitVecConcatOp -> undefined
  -- BitVecZExtOp -> undefined
  -- BitVecSExtOp -> undefined
  -- BitVecSelectOp -> undefined

  op -> const $ throwError_ @SDoc $ "Unsupported PrimOp '" <> ppr op <> "'"
  where
    infix 0 ##
    (##) = call

    unary ty = ty :-> RS ty
    binary ty = ty :-> ty :-> RS ty
    cmp ty = ty :-> ty :-> RS PBool

    bvunary
      :: (forall n. KnownPos n => bv n -> bv n)
      -> Runtime (SomeBitVec bv)
      -> Runtime (SomeBitVec bv)
    bvunary f = fmap \(SomeBitVec bv) -> SomeBitVec (f bv)

    bvbinary
      :: (forall n. KnownPos n => bv n -> bv n -> bv n)
      -> Runtime (SomeBitVec bv)
      -> Runtime (SomeBitVec bv)
      -> Runtime (SomeBitVec bv)
    bvbinary f = bindM2 (bvbinary' f)

    -- TODO: I feel these helpers could be a little bit nicer, but for now I
    -- guess it works.
    bvbinary'
      :: (forall n. KnownPos n => bv n -> bv n -> bv n)
      -> SomeBitVec bv
      -> SomeBitVec bv
      -> Runtime (SomeBitVec bv)
    bvbinary' f (SomeBitVec @l @_ lhs) (SomeBitVec @r @_ rhs) = case eqT @l @r of
      Just Refl -> pure $ SomeBitVec (f lhs rhs)
      Nothing -> mkUndefinedBehaviour

    sbinary
      :: (KnownPos n => SymIntN n -> SymIntN n -> SymIntN n)
      -> (KnownPos n => SymBitVec n -> SymBitVec n -> SymBitVec n)
    sbinary f = toUnsigned .: on f toSigned

    bvcompare
      :: (forall n. KnownPos n => bv n -> bv n -> SymBool)
      -> Runtime (SomeBitVec bv)
      -> Runtime (SomeBitVec bv)
      -> Runtime SymBool
    bvcompare f = bindM2 (bvcompare' f)

    bvcompare'
      :: (forall n. KnownPos n => bv n -> bv n -> SymBool)
      -> SomeBitVec bv
      -> SomeBitVec bv
      -> Runtime SymBool
    bvcompare' f (SomeBitVec @l @_ lhs) (SomeBitVec @r @_ rhs) = case eqT @l @r of
      Just Refl -> pure $ f lhs rhs
      Nothing -> mkUndefinedBehaviour

    scompare
      :: (KnownPos n => SymIntN n -> SymIntN n -> SymBool)
      -> (KnownPos n => SymBitVec n -> SymBitVec n -> SymBool)
    scompare f = on f toSigned

    bindM2 f mx my = do
      x <- mx
      y <- my
      f x y

-- | The primitives we support.
data PrimRep a where
  PBool :: PrimRep SymBool
  PInteger :: PrimRep SymInteger
  PBitVec :: PrimRep (SomeBitVec SymBitVec)
  PPrimTy :: PrimRep SomeLiteralType
  PAny :: PrimRep (Value 'Shared)

instance Outputable (PrimRep a) where
  ppr = \case
    PBool -> "Bool"
    PInteger -> "Integer"
    PBitVec -> "BitVec ?"
    PPrimTy -> "Primitive ?"
    PAny -> "?"

-- | Wrap a value of the given representation into a 'WHNF'.
wrap
  :: HasCallStack
  => Error (LookupError Name) :> es
  => Error (LookupError TH.Name) :> es
  => HasThings :> es
  => Prim :> es
  => THNameToGHCName :> es
  => PrimRep a
  -> Runtime a
  -> Eff es WHNF
wrap @es = \case
  PBool -> pure . fmap (Lit . Bool)
  PInteger -> pure . fmap (Lit . Integer)
  PBitVec -> pure . fmap \(SomeBitVec bv) -> Lit $ BitVec bv
  PPrimTy -> \value -> do
    -- The coercion argument.
    coercionT <- newIORef' $ WHNF (pure coercion)

    -- TODO: This is perhaps better fit as a helper function? It's a bit ugly
    -- as is...
    -- The main wrapping loop.
    let go :: LiteralType a -> Eff es (Value 'Shared)
        go ty = do
          (dc, args) <- case ty of
            BoolType -> pure ('Builtin.BoolType, [])
            IntegerType -> pure ('Builtin.IntegerType, [])
            BitVecType @n -> do
              -- Construct the size argument.
              let size = fromInteger $ natVal @n Proxy
              sizeT <- newIORef' $ WHNF (pure $ Lit (Integer size))

              pure ('Builtin.BitVecType, [sizeT])
            ArrayType keyTy valTy -> do
              key <- go keyTy
              val <- go valTy
              keyT <- newIORef' $ WHNF (pure key)
              valT <- newIORef' $ WHNF (pure val)
              pure ('Builtin.ArrayType, [keyT, valT])
          dc' <- thNameToGhcName >=> lookupDataCon $ dc
          let args' = fromList $ coercionT : args
          pure $ Con (DataCon dc' args')

    -- Construct the expression.
    for value \(SomeLiteralType ty) -> go ty
  PAny -> pure

-- | Unwrap a 'WHNF' into the given representation.
unwrap
  :: HasCallStack
  => Error (LookupError Name) :> es
  => Error (LookupError TH.Name) :> es
  => Error SDoc :> es
  => HasThings :> es
  => Prim :> es
  => Reader PrimOps :> es
  => State Global :> es
  => THNameToGHCName :> es
  => PrimRep a
  -> Thunk
  -> Eff es (Runtime a)
unwrap ty thunk = case ty of
  PBool -> do
    whnf <- force thunk
    pure $ whnf >>= \case
      Lit (Bool value) -> pure value
      _ -> mkUndefinedBehaviour
  PInteger -> do
    whnf <- force thunk
    pure $ whnf >>= \case
      Lit (Integer value) -> pure value
      _ -> mkUndefinedBehaviour
  PBitVec -> do
    whnf <- force thunk
    pure $ whnf >>= \case
      Lit (BitVec value) -> pure $ SomeBitVec value
      _ -> mkUndefinedBehaviour
  PPrimTy -> do
    -- Lookup the possible data constructors in the value.
    let lookupDC = thNameToGhcName >=> lookupDataCon
    boolDC <- lookupDC 'Builtin.BoolType
    intDC <- lookupDC 'Builtin.IntegerType
    bvDC <- lookupDC 'Builtin.BitVecType
    arrDC <- lookupDC 'Builtin.ArrayType

    -- TODO: This is ugly. Perhaps it's better as a helper function outside of
    -- this scope...
    let go thunk' = do
          whnf <- force thunk'
          nested <- for whnf \case
            Con (DataCon dc args)
              | dc == boolDC
              , [_co] <- args -> pure $ pure (SomeLiteralType BoolType)
              | dc == intDC
              , [_co] <- args -> pure $ pure (SomeLiteralType IntegerType)
              | dc == bvDC
              , [_co, sizeT, _pos] <- args -> do
                sizeR <- unwrap PInteger sizeT
                for sizeR \size -> do
                  -- Get a concrete size.
                  size' <- case size of
                    Grisette.Con size' -> pure size'
                    _ -> throwError_ @SDoc "bitvector type expects a concrete size"

                  -- Ensure that it is a positive number.
                  let err = "bitvector type expects a positive size"
                  SomeNat @n _ <- failWith @SDoc err $ someNatVal size'
                  Dict <- failWith @SDoc err $ posNat @n

                  pure $ SomeLiteralType (BitVecType @n)
              | dc == arrDC
              , [_co, keyT, valT] <- args -> do
                keyR <- unwrap PPrimTy keyT
                valR <- unwrap PPrimTy valT
                let arr (SomeLiteralType key) (SomeLiteralType val) = do
                      SomeLiteralType (ArrayType key val)
                pure $ liftA2 arr keyR valR
            _ -> pure mkUndefinedBehaviour
          pure $ join nested

    go thunk
  PAny -> force thunk

-- | Representation of a primitive function.
--
-- A primitive function is always of the form
-- '(Runtime a -> Runtime b -> ... Eff es (Runtime n))'
-- , with the polymorphic arguments being primitives. This data type allows us
-- to define such a function 'a :-> b :-> ... RS n'
data FunRep es a where
  (:->) :: PrimRep a -> FunRep es b -> FunRep es (Runtime a -> b)
  RS :: PrimRep b -> FunRep es (Eff es (Runtime b))

infixr 1 :->

instance Outputable (FunRep es a) where
  ppr = \case
    funTy :-> argTy -> ppr funTy <+> "->" <+> ppr argTy
    RS resTy -> ppr resTy

-- | Apply a function of the supplied representation to the given number of
-- arguments.
--
-- The number of arguments is expected to match the function exactly. A mismatch
-- will result in an error throw.
call
  :: HasCallStack
  => Error (LookupError Name) :> es
  => Error (LookupError TH.Name) :> es
  => Error SDoc :> es
  => HasThings :> es
  => Prim :> es
  => Reader PrimOps :> es
  => State Global :> es
  => THNameToGHCName :> es
  => FunRep es a
  -> a
  -> [Thunk]
  -> Eff es WHNF
call ty spine args = case ty of
  argTy :-> resTy -> do
    (arg, args') <- case args of
      arg : args' -> pure (arg, args')
      [] -> throwError_ @SDoc "Expected argument for function call"
    arg' <- unwrap argTy arg
    let result = spine arg'
    call resTy result args'
  RS resTy -> do
    unless (null args) do
      throwError_ @SDoc "Got argument for non-function call"
    result <- spine
    wrap resTy result

-- TODO: These should probably live adjecent to the type definition. We should
-- remove the current definition of outputable on these types and replace it
-- with a call to 'ppr . With emptyThunks'
instance Outputable (With Thunks Thunk) where
  -- NOTE: We force the 'IORef' object itself to ensure the name is stable.
  ppr (With (Thunks _next thunks) !thunk) = do
    -- TODO: Does it make sense to do 'unsafeDupablePerformIO'?
    let name = unsafePerformIO $ makeStableName thunk
    case HashMap.lookup name thunks of
      Just (idn, _) -> "#" <> ppr idn
      Nothing -> "#?"

instance Outputable (With Thunks ThunkKind) where
  ppr (With thunks kind) = case kind of
    WHNF whnf -> ppr $ With thunks whnf
    Thunk env expr -> sep
      [ ppr $ With thunks env
      , ppr expr
      ]
    Ite guard true false -> hang "ite" 2 $ sep
      [ text $ show guard
      , ppr $ With thunks true
      , ppr $ With thunks false
      ]

instance Outputable (With Thunks WHNF) where
  ppr (With thunks whnf) = pprRuntime (ppr . With thunks) whnf

instance Outputable (With Thunks (Value 'Shared)) where
  ppr (With thunks value) = case value of
    Lit lit -> ppr lit
    Opr op _arity args -> do
      let args' = ppr . With thunks <$> toList args
      hang (ppr op) 2 $ sep args'
    Con con -> ppr $ With thunks con
    Lam env bndr body -> sep
      [ ppr $ With thunks env
      , ppr $ GHC.Lam bndr body
      ]

instance Outputable (With Thunks (Constructor 'Shared)) where
  ppr (With thunks con) = case con of
    DataCon dc args -> do
      let args' = ppr . With thunks <$> toList args
      hang (ppr dc) 2 $ sep args'
    -- TODO: This tag print is bad, should give it an 'Outputable' instance.
    EnumCon tag tc -> sep ["tagToEnum#", ppr tc, text (show tag)]

instance Outputable (With Thunks Env) where
  ppr (With thunks (Env env)) = ppr $ ppr . With thunks <$> env

pprRuntime :: (a -> SDoc) -> Runtime a -> SDoc
pprRuntime @a f rt = do
  let inner _ = \case
        Left bottom -> ppr bottom
        Right value -> f value
  let value = coerce @_ @(Union (Either Bottom a)) rt
  pprUnion inner id value

pprUnion
  :: ((SDoc -> SDoc) -> a -> SDoc)
  -> (SDoc -> SDoc)
  -> Union a
  -> SDoc
pprUnion inner addParens = \case
  Single value -> inner addParens value
  If scrut true false -> do
    -- Pretty print branches.
    let true' = pprUnion inner parens true
    let false' = pprUnion inner parens false

    -- Hange the branches below an if-then-else.
    addParens . hang "ite" 2 $ vcat
      [ text $ show scrut
      , true'
      , false'
      ]

-- | A pair object, with the intent to allow pretty printing of an object under
-- the given environment.
data With env a where
  With :: env -> a -> With env a

-- | A number of thunks.
--
-- The main purpose is to perform a pretty print that can list all thunks.
data Thunks where
  Thunks
    -- | The next identifier for the thunk name.
    :: !Int
    -- | The mapping from a 'Thunk' object to an identifier and its inner value.
    -> !(HashMap (StableName Thunk) (Int, ThunkKind))
    -> Thunks

instance Outputable Thunks where
  ppr thunks@(Thunks _ hm) = do
    let elems = sortBy (on compare fst) $ HashMap.elems hm
    let inner idn kind = "#" <> ppr idn <+> "=" <+> ppr (With thunks kind)
    sep $ uncurry inner <$> elems

-- | Construct an empty list of thunks.
emptyThunks :: Thunks
emptyThunks = Thunks 0 HashMap.empty

-- | Collect the thunks present in the given value.
collectThunks :: CollectThunks a => Prim :> es => a -> Eff es Thunks
collectThunks = execState emptyThunks . collectThunks'

-- | Collect the thunks present in the given value.
class CollectThunks a where
  collectThunks'
    :: State Thunks :> es
    => Prim :> es
    => a
    -> Eff es ()

instance CollectThunks Env where
  -- Collect all thunks in the environment. The order does not matter!
  collectThunks' (Env env) = traverse_ collectThunks' $ NonDetUniqFM env

-- | A wrapper to return an additional value within a functor.
newtype PairF f a b where
  PairF :: { runPairF :: f (a, b) } -> PairF f a b
  deriving Functor

instance CollectThunks Thunk where
  -- NOTE: We force the 'IORef' object itself to ensure the name is stable.
  collectThunks' !thunk = do
    -- TODO: This stable name collection should be an effect! Actually,
    -- if we don't expose the 'Thunks' data structure directly, I think
    -- non-determinism is not broken. We should report on this if we end up
    -- choosing for this!
    -- Fetch the current thunk name and thunk collection.
    name <- unsafeEff_ $ makeStableName thunk
    Thunks next thunks <- get

    -- Check if we already collected this entry. If not, we read the thunk and
    -- create a new hashmap.
    let alter = PairF . MaybeT . \case
          Just _ -> pure Nothing
          Nothing -> do
            kind <- readIORef' thunk
            pure $ Just (kind, Just (next, kind))
    thunksM <- runMaybeT . runPairF $ HashMap.alterF alter name thunks

    -- If the thunk was indeed not added yet, we also need to recursively
    -- traverse the thunks it contains.
    for_ thunksM \(kind, thunks') -> do
      put $ Thunks (next + 1) thunks'
      collectThunks' kind

instance CollectThunks ThunkKind where
  collectThunks' = \case
    WHNF whnf -> collectThunks' whnf
    Thunk env _ -> collectThunks' env
    Ite _guard true false -> do
      collectThunks' true
      collectThunks' false

instance CollectThunks WHNF where
  collectThunks' = traverse_ \case
    Lit _lit -> pure ()
    Opr _op _arity args -> for_ args collectThunks'
    Con con -> collectThunks' con
    Lam env _bndr _body -> collectThunks' env

instance CollectThunks (Constructor 'Shared) where
  collectThunks' = \case
    EnumCon _tag _tc -> pure ()
    DataCon _dc args -> for_ args collectThunks'
