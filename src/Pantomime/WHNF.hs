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
  ) where

import Control.Arrow ((>>>))
import Control.Monad (join, unless)
import Control.Monad.Cont (MonadCont (..), ContT, evalContT)
import Control.Monad.Trans (MonadTrans (lift))
import Control.Monad.Except (ExceptT (..))
import Control.Monad.Except qualified as Except
import Data.Coerce (coerce)
import Data.Composition ((.:))
import Data.Constraint (Dict(..))
import Data.Traversable (for)
import Effectful (Eff, type (:>))
import Effectful.Error.Static (Error, HasCallStack, throwError_)
import Effectful.Prim.IORef.Strict
  ( Prim
  , IORef'
  , readIORef'
  , writeIORef'
  , newIORef'
  )
import Effectful.Reader.Static (ask, Reader)
import Effectful.State.Static.Local (State, get, put)
import GHC.Core qualified as GHC
import GHC.Data.Maybe (whenIsJust)
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
  , lookupVarEnv
  , emptyVarEnv
  , isId
  , unitDataCon
  , extendVarEnv
  , dataConTagZ
  , dataConTyCon
  , isEnumerationTyCon
  )
import GHC.Plugins qualified as GHC
import GHC.IsList (IsList (..))
import GHC.TypeLits (SomeNat (..), someNatVal)
import GHC.Utils.Outputable
  ( SDoc
  , Outputable (..)
  , IsLine ((<+>), text, sep)
  , hang
  , ($+$)
  , nest
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
  , wrapStrategy
  , product2Strategy
  , merge
  , symNot
  , (.&&)
  , (.||)
  )
import Grisette qualified
import Pantomime.Convert (Conversion(..))
import Pantomime.Grisette.Mergeable (impossible)
import Pantomime.Literal (Literal (..))
import Pantomime.PrimOp (PrimOp (..), PrimOps)
import Pantomime.PrimOp qualified as PrimOp
import Pantomime.Orphan.GHC ()
import Pantomime.Orphan.Grisette (pattern Single, pattern If)
import Pantomime.Tsil
import Pantomime.Util (SymBitVec, SomeBitVec (..), foldlBy, failWith, posNat)
import Prelude hiding (rem, (<>), lookup)

type WHNF = WHNF' 'Shared

type WHNF' shr = Runtime (Value shr)

instance Outputable (WHNF' shr) where
  ppr whnf = do
    let inner _ = \case
          Left bottom -> ppr bottom
          Right value -> ppr value
    let value = coerce @_ @(Union (Either Bottom (Value shr))) whnf
    pprUnion inner id value

pprUnion
  :: ((SDoc -> SDoc) -> a -> SDoc)
  -> (SDoc -> SDoc)
  -> Union a
  -> SDoc
pprUnion inner addParens = \case
  Single value -> inner addParens value
  If scrut true false -> do
    -- Vertically concatenate using ($+$).
    let vcat' = foldl' @[] ($+$) GHC.empty

    -- Hang that always aligns vertically.
    let hang' d1 n d2 = vcat' [d1, nest n d2]

    -- Pretty print branches.
    let true' = pprUnion inner parens true
    let false' = pprUnion inner parens false

    -- Hange the branches below an if-then-else.
    addParens . hang' "ite" 2 $ vcat'
      [ text $ show scrut
      , true'
      , false'
      ]

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

-- | Force a thunk to weak-head normal form.
force
  :: HasCallStack
  => Error SDoc :> es
  => Prim :> es
  => Reader Conversion :> es
  => Reader PrimOps :> es
  => State Global :> es
  => Thunk
  -> Eff es WHNF
force thunk = do
  whnf' <- force' thunk
  share whnf'

-- TODO: Callstack growth
-- | Force a thunk to weak-head normal form and keeps it mergeable.
force'
  :: HasCallStack
  => Error SDoc :> es
  => Prim :> es
  => Reader Conversion :> es
  => Reader PrimOps :> es
  => State Global :> es
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

-- | Helper function that runs a single 'callCC' for us and removes the
-- continuation monad afterwards.
withExit :: Monad m => ((r -> ContT r m b) -> ContT r m r) -> m r
withExit = evalContT . callCC

-- TODO: Fix callstack growth.
-- | Evaluate the given closure.
evaluate
  :: HasCallStack
  => Error SDoc :> es
  => Prim :> es
  => Reader Conversion :> es
  => Reader PrimOps :> es
  => State Global :> es
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

    -- Force the conversion function and thunk the argument.
    fun <- evaluate emptyEnv $ GHC.Var convert
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
  GHC.Coercion _ -> do
    -- TODO: Coercions are I think represented as unboxed units in the runtime.
    -- For now, I'll just return a unit constructor. We can see if this needs to
    -- change at some point.
    let unit = pure $ Con (DataCon unitDataCon Lin)
    pure unit
  GHC.Type _ -> throwError_ @SDoc "Cannot evaluate a type."
  GHC.Tick _ body -> evaluate env body

-- | Like evaluate, but leaves the expression in a mergeable state.
evaluate'
  :: HasCallStack
  => Error SDoc :> es
  => Prim :> es
  => Reader Conversion :> es
  => Reader PrimOps :> es
  => State Global :> es
  => Env
  -> CoreExpr
  -> Eff es (WHNF' 'Mergeable)
evaluate' env expr = mergeable <$> evaluate env expr

-- | Apply the function to the argument.
apply
  :: HasCallStack
  => Error SDoc :> es
  => Prim :> es
  => Reader Conversion :> es
  => Reader PrimOps :> es
  => State Global :> es
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
  => Error SDoc :> es
  => Prim :> es
  => Reader Conversion :> es
  => Reader PrimOps :> es
  => State Global :> es
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
  => Reader Conversion :> es
  => GHC.Literal
  -> Eff es (Literal, Id, Id)
literal lit = do
  Conversion { .. } <- ask
  case lit of
    GHC.LitNumber ty num -> do
      let num' :: Num s => s
          num' = fromInteger num
      case ty of
        -- TODO: The bitvector size should be related to the platform size.
        GHC.LitNumInt -> pure (BitVec @64 num', toInt, eqInt)
        GHC.LitNumInt8 -> pure (BitVec @8 num', toInt8, eqInt8)
        GHC.LitNumInt16 -> pure (BitVec @16 num', toInt16, eqInt16)
        GHC.LitNumInt32 -> pure (BitVec @32 num', toInt32, eqInt32)
        GHC.LitNumInt64 -> pure (BitVec @64 num', toInt64, eqInt64)
        GHC.LitNumWord -> pure (BitVec @64 num', toWord, eqWord)
        GHC.LitNumWord8 -> pure (BitVec @8 num', toWord8, eqWord8)
        GHC.LitNumWord16 -> pure (BitVec @16 num', toWord16, eqWord16)
        GHC.LitNumWord32 -> pure (BitVec @32 num', toWord32, eqWord32)
        GHC.LitNumWord64 -> pure (BitVec @64 num', toWord64, eqWord64)
        GHC.LitNumBigNat -> throwError_ @SDoc "TODO: support ByteArray# literal"
    _ -> throwError_ @SDoc $ "Unsupported literal '" <> ppr lit <> "'"

-- | Build a primitive.
--
-- If the primitive is not saturated, we evaluate it. Otherwise, we return the
-- primitive as is.
primitive
  :: HasCallStack
  => Error SDoc :> es
  => Prim :> es
  => Reader Conversion :> es
  => Reader PrimOps :> es
  => State Global :> es
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
  => Error SDoc :> es
  => Prim :> es
  => Reader Conversion :> es
  => Reader PrimOps :> es
  => State Global :> es
  => PrimOp
  -> [Thunk]
  -> Eff es WHNF
primitive' = \case
  -- SymbolicPrimOp -> undefined

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

  BitVecUToIntOp -> PBitVec :-> RS PInteger ## do
    pure . fmap \(SomeBitVec bv) -> symFromIntegral bv
  BitVecSToIntOp -> PBitVec :-> RS PInteger ## do
    pure . fmap \(SomeBitVec @n bv) -> do
      symFromIntegral $ bitCast @_ @(SymIntN n) bv
  -- BitVecSizeOp -> undefined
  -- BitVecNotOp -> undefined
  -- BitVecNegOp -> undefined
  -- BitVecAndOp -> undefined
  -- BitVecOrOp -> undefined
  -- BitVecXorOp -> undefined
  -- BitVecAddOp -> undefined
  -- BitVecMulOp -> undefined
  -- BitVecUDivOp -> undefined
  -- BitVecSDivOp -> undefined
  -- BitVecURemOp -> undefined
  -- BitVecSRemOp -> undefined
  -- BitVecShl -> undefined
  -- BitVecLShr -> undefined
  -- BitVecAShr -> undefined
  -- BitVecEqOp -> undefined
  -- BitVecNeqOp -> undefined
  -- BitVecULeOp -> undefined
  -- BitVecSLeOp -> undefined
  -- BitVecULtOp -> undefined
  -- BitVecSLtOp -> undefined
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

-- | The primitives we support.
data PrimRep a where
  PBool :: PrimRep SymBool
  PInteger :: PrimRep SymInteger
  PBitVec :: PrimRep (SomeBitVec SymBitVec)

-- | Wrap a value of the given representation into a 'WHNF'.
wrap :: PrimRep a -> Runtime a -> WHNF
wrap = \case
  PBool -> fmap $ Lit . Bool
  PInteger -> fmap $ Lit . Integer
  PBitVec -> fmap $ \(SomeBitVec bv) -> Lit $ BitVec bv

-- | Unwrap a 'WHNF' into the given representation.
unwrap :: PrimRep a -> WHNF -> Runtime a
unwrap ty whnf = whnf >>= case ty of
  PBool -> \case
    Lit (Bool value) -> pure value
    _ -> mkUndefinedBehaviour
  PInteger -> \case
    Lit (Integer value) -> pure value
    _ -> mkUndefinedBehaviour
  PBitVec -> \case
    Lit (BitVec value) -> pure $ SomeBitVec value
    _ -> mkUndefinedBehaviour

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

-- | Apply a function of the supplied representation to the given number of
-- arguments.
--
-- The number of arguments is expected to match the function exactly. A mismatch
-- will result in an error throw.
call
  :: HasCallStack
  => Error SDoc :> es
  => Prim :> es
  => Reader Conversion :> es
  => Reader PrimOps :> es
  => State Global :> es
  => FunRep es a
  -> a
  -> [Thunk]
  -> Eff es WHNF
call ty spine args = case ty of
  tyA :-> tyR -> do
    (arg, rem) <- case args of
      arg : rem -> pure (arg, rem)
      [] -> throwError_ @SDoc "Expected argument for function call"
    arg' <- force arg
    let result = spine $ unwrap tyA arg'
    call tyR result rem
  RS tyR -> do
    unless (null args) do
      throwError_ @SDoc "Got argument for non-function call"
    wrap tyR <$> spine
