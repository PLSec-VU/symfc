{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE DeriveGeneric #-}

module Pantomime.WHNF
  ( evaluate

  , Subst
  , emptySubst
  , extendBind

  , pprWHNF
  ) where

import Grisette.Core (Union, Mergeable (..))
import GHC.Plugins
  ( CoreExpr
  , CoreBndr
  , DataCon
  , Id
  , IdEnv
  , lookupVarEnv
  , isLocalId
  , emptyVarEnv
  , isId
  , unitDataCon
  , extendVarEnv
  , CoreAlt
  , dataConTagZ
  , CoreBind
  , dataConTyCon
  , isEnumerationTyCon
  )
import GHC.Utils.Outputable
  ( SDoc
  , Outputable (..)
  , IsLine ((<+>), text, sep)
  , hang, ($+$), nest, parens
  )
import Pantomime.Literal (Literal)
import Pantomime.Util (KnownPos, SymBitVec, failWith, SomeBitVec (..), foldM')
import Prelude hiding ((<>))
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
import Data.Function (on)
import Grisette
  ( SymBool
  , Default (..)
  , MergingStrategy (..)
  , SimpleMergeable (..)
  , wrapStrategy
  , product2Strategy
  , mrgJoin, SymEq ((.==))
  )
import GHC.Generics (Generic (..))
import Pantomime.Grisette.Mergeable (impossible)
import Grisette qualified (LogicalOp (true))

type WHNF = WHNF' 'Shared

-- TODO: Maybe we should newtype it so we can add a ppr? We could also just
-- consider it for 
pprWHNF :: WHNF -> SDoc
pprWHNF whnf = do
  let inner _ = \case
        Left bottom -> ppr bottom
        Right value -> ppr value
  let value = coerce @WHNF @(Union (Either Bottom (Value 'Shared))) whnf
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
share = traverse \case
  Lit lit -> pure $ Lit lit
  Lam closure bndr body -> pure $ Lam closure bndr body
  Con con -> case con of
    EnumCon tag -> pure $ Con (EnumCon tag)
    DataCon dc args -> do
      let go = \case
            Single thunk -> pure thunk
            If guard true false -> do
              true' <- go true
              false' <- go false
              newIORef' $ Ite guard true' false'
      args' <- for args go
      pure $ Con (DataCon dc args')

mergeable :: WHNF -> Eff es (WHNF' 'Mergeable)
mergeable = traverse \case
  Lit lit -> pure $ Lit lit
  Lam closure bndr body -> pure $ Lam closure bndr body
  Con con -> case con of
    EnumCon tag -> pure $ Con (EnumCon tag)
    DataCon dc args -> do
      let args' = Single <$> args
      pure $ Con (DataCon dc args')

data Constructor shr where
  DataCon :: !DataCon -> !(Tsil (Arg shr)) -> Constructor shr
  EnumCon :: KnownPos n => !(SymBitVec n) -> Constructor shr

instance Outputable (Constructor shr) where
  ppr = \case
    DataCon dc args -> do
      hang (ppr dc) 2 $ sep ("<thunk>" <$ toList args)
    -- TODO: This tag print is bad, should give it an 'Outputable' instance.
    EnumCon tag -> "tagToEnum#" <+> text (show tag)

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
        (\(SomeBitVec tag) -> EnumCon tag)
        \case EnumCon tag -> SomeBitVec tag ; _ -> impossible

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

mkBottom :: Bottom -> WHNF
mkBottom = Except.throwError

mkUnreachable :: WHNF
mkUnreachable = mkBottom Unreachable

mkUndefinedBehaviour :: WHNF
mkUndefinedBehaviour = mkBottom UndefinedBehaviour

-- TODO: Probably better to move this somewhere else.
newtype Tsil a where
  Tsil :: [a] -> Tsil a
  deriving Generic
  deriving Mergeable via [a]
  deriving Functor
  deriving Applicative via []
  deriving Monad via []
  deriving Foldable via []

instance Traversable Tsil where
  traverse @_ @a f xs = do
    let xs' = coerce @_ @[a] xs
    coerce <$> traverse f xs'

pattern Lin :: Tsil a
pattern Lin = Tsil []

pattern Snoc :: Tsil a -> a -> Tsil a
pattern Snoc xs x <- Tsil (x : (Tsil -> xs))
  where
    Snoc (Tsil xs) x = Tsil $ x : xs

toList :: Tsil a -> [a]
toList (Tsil xs) = reverse xs

data Subst where
  Subst :: !(IdEnv Thunk) -> Subst

type Thunk = IORef' ThunkKind

data ThunkKind where
  WHNF :: !WHNF -> ThunkKind
  Thunk :: !Subst -> !CoreExpr -> ThunkKind
  Ite :: SymBool -> Thunk -> Thunk -> ThunkKind

force
  :: HasCallStack
  => Prim :> es
  => Error SDoc :> es
  => Subst
  -> Id
  -> Eff es WHNF
force (Subst subst) idn = do
  let go thunk = do
        kind <- readIORef' thunk
        case kind of
          WHNF whnf -> mergeable whnf
          Thunk subst' expr -> do
            whnf <- evaluate subst' expr
            writeIORef' thunk $ WHNF whnf
            mergeable whnf
          Ite guard true false -> do
            true' <- go true
            false' <- go false
            pure $ mrgIte guard true' false'
  let err = "Variable should not be free when trying to force."
  thunk <- failWith @SDoc err $ lookupVarEnv subst idn
  merged <- go thunk
  share merged

extend :: Subst -> Id -> Thunk -> Subst
extend (Subst subst) idn ref = Subst $ extendVarEnv subst idn ref

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
        ref <- newIORef' $ Thunk subst' rhs
        pure (bndr, ref)
      subst' <- pure $ extendMany subst pairs'
    pure subst'

emptySubst :: Subst
emptySubst = Subst emptyVarEnv

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
    | isLocalId var -> force subst var
    -- We create a 'Con' WHNF for any data constructor.
    | Just dc <- GHC.isDataConId_maybe var -> do
      let tc = dataConTyCon dc
      let con = case isEnumerationTyCon tc of
            -- TODO: WHNF for probably have a platform size parameter.
            True -> EnumCon @64 $ fromIntegral (dataConTagZ dc)
            False -> DataCon dc Lin
      pure $ pure @Runtime (Con con)
    -- Evaluate global expressions.
    -- TODO: We should probably create an IORef for these, at least for
    -- non-function globals as GHC stores these as CAFs and we should match
    -- that behaviour.
    | Just expr <- GHC.maybeUnfoldingTemplate $ GHC.realIdUnfolding var -> do
      evaluate emptySubst expr
    | otherwise -> throwError_ @SDoc "Unknown variable."
  GHC.Lit _ -> undefined
  GHC.Lam bndr body
    -- Create a function value.
    | isId bndr -> pure $ pure @Runtime (Lam subst bndr body)
    -- The variable is not computationally relevant, so we elide the function.
    | otherwise -> evaluate subst body
  GHC.App fun arg
    | GHC.isValArg arg -> do
      -- Evaluate the function.
      fun' <- evaluate subst fun

      -- TODO: I guess we could resolve a variable early to safe an extra
      -- redirect thunk allocation? Not sure if it matters much.
      -- We create a new reference once before evaluating the many possible
      -- function calls so we can share the result accross these.
      ref <- newIORef' $ Thunk subst arg

      -- For every lambda, we extend the substitution with the argument and
      -- evaluate the body.
      unmerged <- for fun' \case
        Lam subst' bndr body -> do
          let subst'' = extend subst' bndr ref
          whnf <- evaluate subst'' body
          mergeable whnf
        Con (DataCon dc args) -> do
          let args' = Snoc args ref
          let whnf = pure @Runtime $ Con (DataCon dc args')
          mergeable whnf
        _ -> throwError_ @SDoc "Non function on application."
      share $ mrgJoin unmerged

    -- We elide the application for non computationally relevant arguments.
    | otherwise -> evaluate subst fun
  GHC.Let bind body -> do
    subst' <- extendBind subst bind
    evaluate subst' body
  GHC.Case scrut bndr _ty alts -> do
    -- First we force the scrutinee.
    scrut' <- evaluate subst scrut
    caseOf subst scrut' bndr alts
  GHC.Cast body _ -> evaluate subst body
  GHC.Coercion _ -> do
    -- TODO: Coercions are I think represented as unboxed units in the runtime.
    -- For now, I'll just return a unit constructor. We can see if this needs to
    -- change at some point.
    let unit = pure @Runtime $ Con (DataCon unitDataCon Lin)
    pure unit
  GHC.Type _ -> throwError_ @SDoc "Cannot evaluate a type."
  GHC.Tick _ body -> evaluate subst body

-- TODO: Callstack growth
-- | Find the given 'DataCon' in the alternatives and returns the remaining
-- ones to explore.
--
-- This takes advantage of the sortedness of the alternatives to prune all
-- earlier constructors.
--
-- WARNING: This expects the 'DEFAULT' case to have been stripped from the alts.
matchCon
  :: HasCallStack
  => Error SDoc :> es
  => DataCon
  -> [CoreAlt]
  -> Eff es (Maybe ([CoreBndr], CoreExpr), [CoreAlt])
matchCon dc = \case
  [] -> pure (Nothing, [])
  GHC.Alt (GHC.DataAlt dc') bndrs rhs : alts -> case on compare dataConTagZ dc dc' of
    LT -> matchCon dc alts
    EQ -> pure (Just (bndrs, rhs), alts)
    GT -> pure (Nothing, alts)
  _ -> throwError_ @SDoc "Expected 'DataAlt' as case pattern"

caseOf
  :: HasCallStack
  => Error SDoc :> es
  => Prim :> es
  => Subst
  -> WHNF
  -> CoreBndr
  -> [CoreAlt]
  -> Eff es WHNF
caseOf @es subst scrut0 bndr alts0 = do
  res <- coerce go' alts0' scrut0
  share res
  where
    (alts0', def) = GHC.findDefault alts0

    split :: Union a -> Eff es (SymBool, a, Maybe (Union a))
    split = \case
      If guard (Single true) false -> pure (guard, true, Just false)
      Single end -> pure (Grisette.true, end, Nothing)
      If _ If {} _ -> throwError_ @SDoc "Splitting unmerged union"

    go'
      :: [CoreAlt]
      -> Union (Either Bottom (Value 'Shared))
      -> Eff es (Union (Either Bottom (Value 'Mergeable)))
    go' alts scrut = do
      (guard, leafT, remF) <- split scrut

      (true, alts') <- case leafT of
        -- We can always match the default case, no matter what type of
        -- scrutinee this is.
        _ | [] <- alts -> do
          rhs <- case def of
            Just rhs -> coerce do
              -- TODO: This scrutinee should include other non-matching
              -- branches...
              ref <- newIORef' $ WHNF (coerce scrut)
              let subst' = extend subst bndr ref
              rhs' <- evaluate subst' rhs
              mergeable rhs'
            Nothing -> pure $ pure (Left UndefinedBehaviour)
          pure (rhs, [])
        -- We can just skip past bottom values.
        Left bottom -> pure (pure $ Left bottom, alts)
        -- TODO: We should do something else for literals. This should probably
        -- be checked before, as a literal can actually match these due to
        -- embeddings.
        -- We can actually match on EnumCon and DataCon.
        Right value -> case value of
          Con con -> case con of
            EnumCon tag
              | Nothing <- remF -> do
                base <- case def of
                  Just rhs -> coerce do
                    ref <- newIORef' $ WHNF (coerce scrut)
                    let subst' = extend subst bndr ref
                    rhs' <- evaluate subst' rhs
                    mergeable rhs'
                  Nothing -> pure $ pure (Left UndefinedBehaviour)
                rhs <- foldM' base alts \acc (GHC.Alt ac bndrs rhs) -> do
                  dc <- case ac of
                    GHC.DataAlt dc | [] <- bndrs -> pure dc
                    _ -> throwError_ @SDoc "Expected enum alt"
                  let dc' = fromIntegral $ GHC.dataConTagZ dc
                  ref <- newIORef' $ WHNF (pure $ Con (EnumCon dc'))
                  let subst' = extend subst bndr ref
                  rhs' <- evaluate subst' rhs
                  rhs'' <- mergeable rhs'
                  pure $ mrgIte (tag .== dc') (coerce rhs'') acc
                pure (rhs, [])
              | otherwise -> throwError_ @SDoc "Unmerged enumeration constructor"
            DataCon dc args -> do
              (match, alts') <- matchCon dc alts
              rhs <- case match of
                Just (bndrs, rhs) -> do
                  -- We know the scrutinee can only be this value, so we set
                  -- the case binder as such to restrict the state space.
                  let scrut' = pure $ Con (DataCon dc args)
                  ref <- newIORef' $ WHNF scrut'
                  let subst' = extend subst bndr ref

                  -- Substitute the binders of the pattern.
                  let bndrs' = filter isId bndrs
                  let args' = toList args
                  let subst'' = extendMany subst' $ zip bndrs' args'

                  -- Evaluate the alternative with the new substitution.
                  rhs' <- evaluate subst'' rhs
                  coerce mergeable rhs'
                Nothing -> undefined
              pure (rhs, alts')
          _ -> throwError_ @SDoc "Cannot match on non-DataCon"

      case remF of
        Nothing -> pure true
        Just remF' -> do
          false <- go' alts' remF'
          pure $ If guard true false
