module Pantomime.WHNF
  ( WHNF
  , Bottom
  , mkBottom
  , mkUnreachable
  , mkUndefinedBehaviour

  , evaluate

  , Subst
  , emptySubst
  , extendBind
  ) where

import Grisette.Core (Union, Mergeable (..))
import GHC.Plugins
  ( CoreExpr
  , CoreBndr
  , DataCon
  , Id
  , IdEnv
  , CoreAlt
  , CoreBind
  , lookupVarEnv
  , isLocalId
  , emptyVarEnv
  , isId
  , unitDataCon
  , extendVarEnv
  , dataConTagZ
  , dataConTyCon
  , isEnumerationTyCon
  , TyCon
  , IsLine ((<>))
  )
import GHC.Utils.Outputable
  ( SDoc
  , Outputable (..)
  , IsLine ((<+>), text, sep)
  , hang
  , ($+$)
  , nest
  , parens
  )
import Pantomime.Literal (Literal)
import Pantomime.Util
  ( SymBitVec
  , foldlBy
  )
import Prelude hiding ((<>), lookup)
import GHC.Core qualified as GHC
import Control.Monad.Except (ExceptT (..))
import Effectful (Eff, type (:>))
import Effectful.Prim.IORef.Strict
  ( Prim
  , IORef'
  , readIORef'
  , writeIORef'
  , newIORef'
  )
import Effectful.Error.Static (Error, HasCallStack, throwError_)
import GHC.Plugins qualified as GHC
import Data.Traversable (for)
import Pantomime.Orphan.Grisette (pattern Single, pattern If)
import Pantomime.Orphan.GHC ()
import Control.Monad.Except qualified as Except
import Data.Coerce (coerce)
import Grisette
  ( SymBool
  , Default (..)
  , MergingStrategy (..)
  , SimpleMergeable (..)
  , wrapStrategy
  , product2Strategy
  , SymEq ((.==))
  , merge
  )
import GHC.Generics (Generic (..))
import Pantomime.Grisette.Mergeable (impossible)
import Pantomime.Tsil
import Control.Monad (join)
import Control.Arrow ((>>>))
import Control.Monad.Trans (MonadTrans(lift))

type WHNF = WHNF' 'Shared

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

type WHNF' shr = Runtime (Value shr)

type Runtime = ExceptT Bottom Union

data Value shr where
  Lit :: !Literal -> Value shr
  Con :: !(Constructor shr) -> Value shr
  Lam :: !Subst -> !Id -> !CoreExpr -> Value shr
  deriving Generic

instance Outputable (Value shr) where
  ppr = \case
    Lit lit -> ppr lit
    Con con -> ppr con
    Lam _closure bndr body -> ppr $ GHC.Lam bndr body

instance Mergeable (Value 'Mergeable) where
  rootStrategy = SortedStrategy @Int
    (\case
      Lit {} -> 0
      Con {} -> 1
      Lam {} -> 2)
    \case
      0 -> wrapStrategy
        rootStrategy
        Lit
        \case Lit lit -> lit ; _ -> impossible
      1 -> wrapStrategy
        rootStrategy
        Con
        \case Con con -> con ; _ -> impossible
      2 -> NoStrategy
      _ -> impossible

share :: Prim :> es => WHNF' 'Mergeable -> Eff es WHNF
share = merge >>> traverse \case
  Lit lit -> pure $ Lit lit
  Lam closure bndr body -> pure $ Lam closure bndr body
  Con con -> case con of
    EnumCon tag tc -> pure $ Con (EnumCon tag tc)
    DataCon dc args -> do
      let go = \case
            Single thunk -> pure thunk
            If guard true false -> do
              true' <- go true
              false' <- go false
              newIORef' $ Ite guard true' false'
      args' <- for args go
      pure $ Con (DataCon dc args')

mergeable :: WHNF -> WHNF' 'Mergeable
mergeable = fmap \case
  Lit lit -> Lit lit
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
    DataCon dc args -> do
      hang (ppr dc) 2 $ sep ("<thunk>" <$ toList args)
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
type family Arg (stage :: Sharing) where
  Arg 'Mergeable = Union Thunk
  Arg 'Shared = Thunk

data Sharing where
  Mergeable :: Sharing
  Shared :: Sharing

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

mkBottom :: Bottom -> WHNF' shr
mkBottom = Except.throwError

mkUnreachable :: WHNF' shr
mkUnreachable = mkBottom Unreachable

mkUndefinedBehaviour :: WHNF' shr
mkUndefinedBehaviour = mkBottom UndefinedBehaviour

newtype Subst where
  Subst :: IdEnv Thunk -> Subst

instance Outputable Subst where
  ppr (Subst subst) = ppr $ fmap (const @SDoc "<thunk>") subst

emptySubst :: Subst
emptySubst = Subst emptyVarEnv

lookup :: Subst -> Id -> Maybe Thunk
lookup = coerce $ lookupVarEnv @Thunk

extend :: Subst -> Id -> Thunk -> Subst
extend = coerce $ extendVarEnv @Thunk

extendMany :: Foldable f => Subst -> f (Id, Thunk) -> Subst
extendMany = foldl' $ uncurry . extend

extendBind
  :: Prim :> es
  => Subst
  -> CoreBind
  -> Eff es Subst
extendBind subst = \case
  GHC.NonRec bndr body -> do
    ref <- newIORef' $ Thunk subst body
    pure $ extend subst bndr ref
  GHC.Rec pairs -> do
    rec
      pairs' <- for pairs \(bndr, rhs) -> do
        -- NOTE: We need to pass in the new substitution with all binders
        -- present. We use the fixpoint computation for this purpose.
        thunk <- newIORef' $ Thunk subst' rhs
        pure (bndr, thunk)
      subst' <- pure $ extendMany subst pairs'
    pure subst'

type Thunk = IORef' ThunkKind

data ThunkKind where
  WHNF :: !WHNF -> ThunkKind
  Thunk :: !Subst -> !CoreExpr -> ThunkKind
  Ite :: SymBool -> Thunk -> Thunk -> ThunkKind

-- TODO: Callstack growth
force'
  :: HasCallStack
  => Prim :> es
  => Error SDoc :> es
  => Thunk
  -> Eff es (WHNF' 'Mergeable)
force' thunk = do
  kind <- readIORef' thunk
  case kind of
    WHNF whnf -> pure $ mergeable whnf
    Thunk subst' expr -> do
      whnf <- evaluate subst' expr
      writeIORef' thunk $ WHNF whnf
      pure $ mergeable whnf
    Ite guard true false -> do
      true' <- force' true
      false' <- force' false
      pure $ mrgIte guard true' false'

force
  :: HasCallStack
  => Prim :> es
  => Error SDoc :> es
  => Thunk
  -> Eff es WHNF
force thunk = do
  whnf' <- force' thunk
  share whnf'

-- TODO: Fix callstack growth.
evaluate
  :: HasCallStack
  => Prim :> es
  => Error SDoc :> es
  => Subst
  -> CoreExpr
  -> Eff es WHNF
evaluate subst = \case
  GHC.Var var
    -- Local variables should be in the substitution.
    | isLocalId var
    , Just thunk <- lookup subst var -> force thunk
    -- We create a 'Con' WHNF for any data constructor.
    | Just dc <- GHC.isDataConId_maybe var -> do
      let tc = dataConTyCon dc
      let con = case isEnumerationTyCon tc of
            -- TODO: WHNF should probably have a platform size parameter as a
            -- universal quantifier.
            True -> EnumCon (fromIntegral $ dataConTagZ dc) tc
            False -> DataCon dc Lin
      pure $ pure (Con con)
    -- Evaluate global expressions.
    -- TODO: We should probably create an IORef for these, at least for
    -- non-function globals as GHC stores these as CAFs and we should match
    -- that behaviour.
    | Just expr <- GHC.maybeUnfoldingTemplate $ GHC.realIdUnfolding var -> do
      evaluate emptySubst expr
    | otherwise -> throwError_ @SDoc $ "Unknown variable '" <> ppr var <> "'"
  GHC.Lit _ -> throwError_ @SDoc "TODO: Implement literals!"
  GHC.Lam bndr body
    -- Create a function value.
    | isId bndr -> pure $ pure (Lam subst bndr body)
    -- The variable is not computationally relevant, so we elide the function.
    | otherwise -> evaluate subst body
  GHC.App fun arg
    | GHC.isValArg arg -> do
      -- Evaluate the function.
      fun' <- evaluate subst fun

      -- We create a new reference once before evaluating the many possible
      -- function calls so we can share the result accross these.
      ref <- newIORef' $ Thunk subst arg

      -- For every lambda, we extend the substitution with the argument and
      -- evaluate the body.
      unmerged <- for fun' \case
        Lam subst' bndr body -> do
          let subst'' = extend subst' bndr ref
          evaluate' subst'' body
        Con (DataCon dc args) -> do
          let args' = Snoc args ref
          let whnf = pure $ Con (DataCon dc args')
          pure $ mergeable whnf
        _ -> pure mkUndefinedBehaviour
      share $ join unmerged
    -- We elide the application for non computationally relevant arguments.
    | otherwise -> evaluate subst fun
  GHC.Let bind body -> do
    subst' <- extendBind subst bind
    evaluate subst' body
  GHC.Case scrut bndr _ty alts -> do
    -- First we force the scrutinee.
    scrut' <- evaluate subst scrut

    -- Split the default pattern, if any.
    let (alts', def) = GHC.findDefault alts

    -- We start by grouping values that take the same path. This way, we will
    -- only evaluate the right-hand-side of each alternative at most once.
    let grouped = merge do
          value <- scrut'
          lift $ match value alts'

    -- Evaluate the grouped alternatives.
    unmerged <- for grouped $ branch subst bndr def

    -- Join the branches and make them shareable.
    share $ join unmerged
  GHC.Cast body _ -> evaluate subst body
  GHC.Coercion _ -> do
    -- TODO: Coercions are I think represented as unboxed units in the runtime.
    -- For now, I'll just return a unit constructor. We can see if this needs to
    -- change at some point.
    let unit = pure $ Con (DataCon unitDataCon Lin)
    pure unit
  GHC.Type _ -> throwError_ @SDoc "Cannot evaluate a type."
  GHC.Tick _ body -> evaluate subst body

evaluate'
  :: HasCallStack
  => Prim :> es
  => Error SDoc :> es
  => Subst
  -> CoreExpr
  -> Eff es (WHNF' 'Mergeable)
evaluate' subst expr = mergeable <$> evaluate subst expr

data Alt where
  DataAlt :: DataCon -> [(CoreBndr, Thunk)] -> CoreExpr -> Alt
  DEFAULT :: WHNF' 'Mergeable -> Alt
  -- | Triggered whenever type confusion happened and no alternative could be
  -- selected.
  --
  -- This could be due to existential types or (broken) unsafe code .
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
      -- That is, they are already merged. This data type only exists to merge
      -- default branches before evaluation of the branch.
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
-- WARNING: The given alternatives are expected to be stripped of the default
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
        let bndrs' = zip bndrs $ toList args
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
  => Subst
  -- ^ The current variables in scope.
  -> CoreBndr
  -- ^ The case binder.
  -> Maybe CoreExpr
  -- ^ Default branch, if available.
  -> Alt
  -- ^ The alternative to evaluate.
  -> Eff es (WHNF' 'Mergeable)
branch subst bndr def = \case
  -- Evaluate the data constructor alternative.
  DataAlt dc bndrs rhs -> do
    let tc = dataConTyCon dc
    let scrut' = pure $ Con case isEnumerationTyCon tc of
          True -> EnumCon (fromIntegral $ dataConTagZ dc) tc
          False -> DataCon dc $ fromList (snd <$> bndrs)
    thunk <- newIORef' $ WHNF scrut'
    let subst' = extendMany subst $ (bndr, thunk) : bndrs
    evaluate' subst' rhs

  -- Evaluate the default alternative, if there is a default case exists.
  DEFAULT scrut' | Just rhs <- def -> do
    scrut'' <- share scrut'
    thunk <- newIORef' $ WHNF scrut''
    let subst' = extend subst bndr thunk
    evaluate' subst' rhs

  -- No match, so we get 'UndefinedBehaviour' for this branch.
  _ -> pure mkUndefinedBehaviour
