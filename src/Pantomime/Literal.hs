{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}

module Pantomime.Literal
  -- | The primary export of this module.
  --
  -- This contains the 'Literal' itself as well as its type and typeclass
  -- constraint.
  ( Literal (Literal, Bool, Integer, BitVec, Array)
  , LiteralTypeable (..)
  , HasDict (..)
  , literalTypeOf
  , LiteralType (..)
  , eqLiteralType
  , SomeLiteralType (..)
  , SomeArray (..)

  -- | Conversion between 'LiteralType' and 'Type'.
  , BuiltInTyCon (..)
  , embedLitTy
  , embedSomeLitTy
  , embedLitTyOf
  , projectLitTy
  ) where

import Control.Applicative (Alternative(..))
import Control.Monad ((>=>))

import Data.Constraint (Dict (..), HasDict (..), withDict)
import Data.Functor.Identity (Identity(..))
import Data.Maybe (isJust)
import Data.Proxy (Proxy(..))
import Data.Typeable (Typeable, type (:~:) (..), eqT)

import Effectful
import Effectful.Context
import Effectful.Error.Static

import GHC.Core.Class (Class)
import GHC.Core.Reduction (Reduction(..))
import GHC.Core.FamInstEnv (normaliseType, FamInstEnvs)
import GHC.Plugins
  ( Type
  , TyCon
  , CoercionN
  , Role (..)
  , Outputable (..)
  , SDoc
  , IsLine (..)
  , text
  , mkTyConTy
  , mkNumLitTy
  , mkTyConApp
  , splitTyConApp_maybe
  , isNumLitTy
  , parens
  )
import GHC.TypeLits (SomeNat (..), natVal, someNatVal)

import Grisette
  ( SymBool
  , SymInteger
  , Solvable
  , ConRep(..)
  , LinkedRep
  , Mergeable (..)
  , SimpleMergeable (..)
  , MergingStrategy (..)
  , EvalSym (..)
  )
-- TODO: Remove internal import once we fix Grisette API.
import Grisette.Internal.SymPrim.Prim.Term (SupportedNonFuncPrim)
import Grisette.Internal.SymPrim.SymArray (SymArray)

import Pantomime.Util (KnownPos, SymBitVec, failWith, posNat)
import Pantomime.Grisette.Mergeable (impossible)

class
  -- TODO: I'm not sure if I should have these here or somewhere else, as we can
  -- also reify them from just LiteralType. I guess this is the most ergonomic?
  ( SupportedNonFuncPrim (ConType a)
  , LinkedRep (ConType a) a
  , Solvable (ConType a) a
  , SimpleMergeable a
  , EvalSym a
  , Typeable a
  -- TODO: I want to switch away from show, into Outputable. Maybe I should just
  -- get an Outputable instance for Literal though, as these types actually
  -- don't have an instance themselves.
  , Show a
  )
  => LiteralTypeable a where
  literalType :: LiteralType a

instance LiteralTypeable SymBool where
  literalType = BoolType

instance LiteralTypeable SymInteger where
  literalType = IntegerType

instance KnownPos n => LiteralTypeable (SymBitVec n) where
  literalType = BitVecType

instance
  ( LiteralTypeable k
  , LiteralTypeable v
  )
  => LiteralTypeable (SymArray k v) where
  literalType = ArrayType literalType literalType

-- | Get the 'LiteralType' for the given instance.
literalTypeOf :: LiteralTypeable a => a -> LiteralType a
literalTypeOf _ = literalType

-- TODO: There are more literal types to consider here. At the very least floats
-- and sequences. I don't think we would want ADT or functions here, as they
-- can also be encoded in the expression language already. We can reconsider it
-- later perhaps. I guess if we want to put ADT or functions inside of an array
-- or sequence, then maybe we do need to support it though. I'm not sure how to
-- handle that yet.
-- | The type of literals supported within the symbolic executor.
--
-- This is like a version of 'TypeRep' for a fixed domain of types.
data LiteralType a where
  BoolType
    :: LiteralType SymBool
  IntegerType
    :: LiteralType SymInteger
  BitVecType
    :: KnownPos n
    => LiteralType (SymBitVec n)
  ArrayType
    :: LiteralType k
    -> LiteralType v
    -> LiteralType (SymArray k v)

instance Outputable (LiteralType a) where
  ppr = pprLitTy id

instance Eq (LiteralType a) where
  (==) _ _ = True

instance Ord (LiteralType a) where
  compare _ _ = EQ

instance Mergeable (LiteralType a) where
  rootStrategy = SimpleStrategy mrgIte

instance SimpleMergeable (LiteralType a) where
  mrgIte _ value _ = value

instance HasDict (LiteralTypeable a) (LiteralType a) where
  evidence = \case
    BoolType -> Dict
    IntegerType -> Dict
    BitVecType -> Dict
    ArrayType keyTy valTy -> runIdentity do
      Dict <- pure $ evidence keyTy
      Dict <- pure $ evidence valTy
      pure Dict

pprLitTy :: (SDoc -> SDoc) -> LiteralType a -> SDoc
pprLitTy par = \case
  BoolType -> "Bool"
  IntegerType -> "Integer"
  BitVecType @n -> par $ "BitVec" <+> ppr (natVal @n Proxy)
  ArrayType k v -> par $ "Array" <+> pprLitTy parens k <+> pprLitTy parens v

eqLiteralType :: LiteralType a -> LiteralType b -> Maybe (a :~: b)
eqLiteralType = \cases
  BoolType BoolType -> pure Refl
  IntegerType IntegerType -> pure Refl
  (BitVecType @nl) (BitVecType @nr) -> do
    Refl <- eqT @nl @nr
    pure Refl
  (ArrayType keyTyL valTyL) (ArrayType keyTyR valTyR) -> do
    Refl <- eqLiteralType keyTyL keyTyR
    Refl <- eqLiteralType valTyL valTyR
    pure Refl
  _ _ -> empty

data SomeLiteralType where
  SomeLiteralType :: !(LiteralType a) -> SomeLiteralType

instance Outputable SomeLiteralType where
  ppr (SomeLiteralType ty) = "SomeLiteralType:" <+> pprLitTy parens ty

instance Eq SomeLiteralType where
  SomeLiteralType lhs == SomeLiteralType rhs = isJust $ eqLiteralType lhs rhs

instance Ord SomeLiteralType where
  compare (SomeLiteralType lhs) (SomeLiteralType rhs) = case (lhs, rhs) of
    (BoolType, BoolType) -> EQ
    (BoolType, _) -> GT
    (_, BoolType) -> LT

    (IntegerType, IntegerType) -> EQ
    (IntegerType, _) -> GT
    (_, IntegerType) -> LT

    (BitVecType @nl, BitVecType @nr) -> do
      let nL = natVal @nl Proxy
      let nR = natVal @nr Proxy
      compare nL nR
    (BitVecType, _) -> GT
    (_, BitVecType) -> LT

    (ArrayType keyTyL valTyL, ArrayType keyTyR valTyR) -> do
      let lhs' = (SomeLiteralType keyTyL, SomeLiteralType valTyL)
      let rhs' = (SomeLiteralType keyTyR, SomeLiteralType valTyR)
      compare lhs' rhs'

instance Mergeable SomeLiteralType where
  rootStrategy = SortedStrategy id $ \_ -> SimpleStrategy \_ value _ -> value

-- | Symbolic literals supported by the symbolic execution engine.
data Literal where
  Literal :: LiteralType a -> a -> Literal

instance Outputable Literal where
  -- TODO: We are printing the grisette primitives using show which is
  -- oblivious to indentation. We should make an actual pretty printer for
  -- symbolic variables. Ideally, the variable names get the pretty printing
  -- that is similar to how their naming works in the fresh variable
  -- generation.
  ppr (Literal ty value) = withDict ty $ text (show value)

instance Mergeable Literal where
  rootStrategy = SortedStrategy
    (\(Literal ty _value) -> SomeLiteralType ty)
    \_ -> SimpleStrategy \cases
      scrut (Literal lty lval) (Literal rty rval)
        | Just Refl <- eqLiteralType lty rty
        , Dict <- evidence lty -> do
          Literal lty $ mrgIte scrut lval rval
      _ _ _ -> impossible

instance EvalSym Literal where
  evalSym fill model (Literal ty value) = runIdentity do
    Dict <- pure $ evidence ty
    let value' = evalSym fill model value
    pure $ Literal ty value'

-- | Boolean pattern for 'Literal'.
pattern Bool :: SymBool -> Literal
pattern Bool value = Literal BoolType value

-- | Integer pattern for 'Literal'.
pattern Integer :: SymInteger -> Literal
pattern Integer value = Literal IntegerType value

-- | BitVec pattern for 'Literal'.
pattern BitVec :: () => KnownPos n => SymBitVec n -> Literal
pattern BitVec value = Literal BitVecType value

-- | Array pattern for 'Literal'.
pattern Array
  :: () =>
   ( LiteralTypeable k
   , LiteralTypeable v
   )
  => SymArray k v
  -> Literal
pattern Array value <- (viewArray -> Just (SomeArray value))
  where
    Array value = Literal (ArrayType literalType literalType) value

{-# COMPLETE Bool, Integer, BitVec, Array #-}

-- | Helper data type for pattern synonym 'Array'.
data SomeArray where
  SomeArray
    :: forall k v.
     ( LiteralTypeable k
     , LiteralTypeable v
     )
    => SymArray k v
    -> SomeArray

-- | Helper view pattern for pattern synonym 'Array'.
viewArray :: Literal -> Maybe SomeArray
viewArray = \case
  Literal (ArrayType keyTy valTy) value -> do
    Dict <- pure $ evidence keyTy
    Dict <- pure $ evidence valTy
    pure $ SomeArray value
  _ -> empty

-- TODO: Perhaps we should probably move this one outside of literal, as it
-- contains TyCon also not for literals.
-- TODO: I feel like this should be an effect and not a data structure,
-- especially since these lookups would in fact all be funnelled by the
-- template Haskell lookup stuff anyway (which has a cache, so is fast!).
-- TODO: One other thing we should do is report a bug with the BuiltInTyCon
-- name. Somehow, the compiler crashes if you use this name in particular as
-- DataCon without importing the DataCon itself (I.e. only the TyCon is in
-- scope). I think this is a GHC issue.
-- | Built-in type constructors.
data BuiltInTyCon where
  BuiltInTyCon ::
    { tcBool :: TyCon
    , tcInteger :: TyCon
    , tcBitVec :: TyCon
    , tcArray :: TyCon
    , tcPrimitive :: TyCon
    , tcKnownNat :: TyCon
    , tcLEqNat :: TyCon
    , tcUnsafeEquality :: TyCon
    , clsEmbeddable :: Class
    } -> BuiltInTyCon

-- | Convert a 'LiteralType' into a Haskell 'Type'.
embedLitTy
  :: Context Reader BuiltInTyCon :> es
  => LiteralType a
  -> Eff es Type
embedLitTy ty = do
  -- TODO: I feel like this is not the best way to have the effect. Probably we
  -- just want to wrap the other lookup effect stack!
  BuiltInTyCon { .. } <- get
  case ty of
    BoolType -> pure $ mkTyConTy tcBool
    IntegerType -> pure $ mkTyConTy tcInteger
    BitVecType @n -> do
      let nTy = mkNumLitTy $ natVal @n Proxy
      pure $ mkTyConApp tcBitVec [nTy]
    ArrayType keyTy valTy -> do
      keyTy' <- embedLitTy keyTy
      valTy' <- embedLitTy valTy
      pure $ mkTyConApp tcArray [keyTy', valTy']

-- | Convert a 'SomeLiteralType' into a Haskell 'Type'.
embedSomeLitTy
  :: Context Reader BuiltInTyCon :> es
  => SomeLiteralType
  -> Eff es Type
embedSomeLitTy (SomeLiteralType ty) = embedLitTy ty

-- | Convert the 'LiteralType' of a 'Literal' into a Haskell 'Type'.
embedLitTyOf
  :: Context Reader BuiltInTyCon :> es
  => Literal
  -> Eff es Type
embedLitTyOf (Literal ty _) = embedLitTy ty

-- | Fetch a 'LiteralType' from a GHC 'Type', if possible.
--
-- This additionally return a nominal coercion for all type-families that were
-- reduced.
projectLitTy
  :: HasCallStack
  => Error String :> es
  => Context Reader BuiltInTyCon :> es
  => Context Reader FamInstEnvs :> es
  => Type
  -> Eff es (CoercionN, SomeLiteralType)
projectLitTy ty = do
  fam <- get @FamInstEnvs
  -- NOTE: Altough normalising the entire term is slow, we only really do this
  -- if we actually force the entire type within reifyLitType (in which case, we
  -- needed to normalise anyway).
  let Reduction co ty' = normaliseType fam Nominal ty
  lty <- projectLitTy' ty'
  pure (co, lty)

-- | Helper function for 'reifyLitType'.
--
-- This will reify the 'LiteralType' from a GHC 'Type' only if it is free from
-- any type families or aliases.
projectLitTy'
  :: HasCallStack
  => Error String :> es
  => Context Reader BuiltInTyCon :> es
  => Type
  -> Eff es SomeLiteralType
projectLitTy' ty = do
  -- TODO: We should fix the recursive callstack grow!
  (tc, targs) <- failWith @String "projectLitTy': expected a TyCon application" $ splitTyConApp_maybe ty
  BuiltInTyCon { .. } <- get
  if
    | tc == tcBool
    , [] <- targs -> pure $ SomeLiteralType BoolType

    | tc == tcInteger
    , [] <- targs -> pure $ SomeLiteralType IntegerType

    | tc == tcBitVec
    , [narg] <- targs -> do
      let knownNatTy = isNumLitTy >=> someNatVal
      SomeNat @n _ <- failWith @String "projectLitTy': expected a KnownNat literal" $ knownNatTy narg
      Dict <- failWith @String "projectLitTy': expected a positive Nat for BitVec size" $ posNat @n
      pure $ SomeLiteralType (BitVecType @n)

    | tc == tcArray
    , [keyTy, valTy] <- targs -> do
      SomeLiteralType keyTy' <- projectLitTy' keyTy
      SomeLiteralType valTy' <- projectLitTy' valTy
      pure $ SomeLiteralType (ArrayType keyTy' valTy')

    | otherwise -> throwError @String "projectLitTy': unsupported literal type"
