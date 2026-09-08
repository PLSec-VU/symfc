{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}

-- | This module contains orphan instances for GHC data types.
--
-- Specifically, we wish to place GHC types inside of a Grisette Union, which
-- requires the 'Mergeable' typeclass instance.
module Pantomime.Orphan.GHC
  ( Generically (..)
  , Uniquely (..)
  ) where

import GHC.Plugins
  ( Uniquable(..)
  , Specificity (..)
  , TyCon
  , DataCon
  , FastString
  , Var
  , VarBndr (..)
  , Role
  , coercionKindRole
  , dataConTyCon
  , dataConTagZ
  )
import GHC.Core.TyCo.Rep
  ( Type (..)
  , ForAllTyFlag (..)
  , FunTyFlag (..)
  , TyLit (..)
  , Coercion (..)
  , Scaled (..)
  )
import GHC.Data.Pair (unPair)
import GHC.Types.Unique (getKey, eqUnique, nonDetCmpUnique)

import Grisette
  ( Mergeable (..)
  , MergingStrategy (..)
  , Default (..)
  , EvalSym (..)
  )

import Data.Function (on)
import Control.Arrow (Arrow(..))
import GHC.Generics (Generic (..))

-- | Newtype for deriving comparison via generics.
newtype Generically a where
  Generically :: a -> Generically a

-- | This is a hack to implicitly wrap/unwrap in the instances of 'Generically'.
instance Generic a => Generic (Generically a) where
  type Rep (Generically a) = Rep a
  to = Generically . to
  from (Generically x) = from x

instance (Generic a, Eq (Rep a ())) => Eq (Generically a) where
  (==) = geq

instance (Generic a, Ord (Rep a ())) => Ord (Generically a) where
  compare = gcompare

geq :: forall a. Generic a => Eq (Rep a ()) => a -> a -> Bool
geq = (==) `on` from @a @()

gcompare :: forall a. Generic a => Ord (Rep a ()) => a -> a -> Ordering
gcompare = compare `on` from @a @()

-- | Newtype for deriving comparison and merging via its 'Uniquable' instance.
newtype Uniquely a where
  Uniquely :: a -> Uniquely a

instance Uniquable a => Uniquable (Uniquely a) where
  getUnique (Uniquely value) = getUnique value

instance Uniquable a => Eq (Uniquely a) where
  (==) = eqUnique `on` getUnique

instance Uniquable a => Ord (Uniquely a) where
  compare = nonDetCmpUnique `on` getUnique

instance Uniquable a => Mergeable (Uniquely a) where
  rootStrategy = SortedStrategy
    (getKey . getUnique)
    (\_idx -> SimpleStrategy \_cond lhs _rhs -> lhs)

deriving via Uniquely Var instance Mergeable Var

deriving via Uniquely TyCon instance Ord TyCon
deriving via Uniquely TyCon instance Mergeable TyCon

instance Ord DataCon where
  compare lhs rhs = case on compare (Uniquely . dataConTyCon) lhs rhs of
    EQ -> on compare dataConTagZ lhs rhs
    result -> result

instance Mergeable DataCon where
  rootStrategy = SortedStrategy
    (getKey . getUnique . dataConTyCon)
    \_idx -> SortedStrategy
      dataConTagZ
      \_idx -> SimpleStrategy \_cond lhs _rhs -> lhs

deriving via Uniquely FastString instance Ord FastString
deriving via Uniquely FastString instance Mergeable FastString

deriving instance Generic (VarBndr var argf)
deriving via Default (VarBndr var argf)
  instance (Mergeable var, Mergeable argf) => Mergeable (VarBndr var argf)

deriving instance Generic TyLit
deriving via Generically TyLit instance Ord TyLit
deriving via Default TyLit instance Mergeable TyLit

deriving instance Generic Specificity
deriving via Default Specificity instance Mergeable Specificity

deriving instance Generic ForAllTyFlag
deriving via Default ForAllTyFlag instance Mergeable ForAllTyFlag

deriving instance Generic FunTyFlag
deriving via Default FunTyFlag instance Mergeable FunTyFlag

deriving instance Generic Type
deriving via Default Type instance Mergeable Type
deriving via Generically Type instance Eq Type
deriving via Generically Type instance Ord Type

instance EvalSym Type where
  evalSym _ _ = id

deriving instance Generic (Scaled a)
deriving via Default (Scaled a) instance Mergeable a => Mergeable (Scaled a)
deriving via Generically (Scaled a) instance Eq a => Eq (Scaled a)
deriving via Generically (Scaled a) instance Ord a => Ord (Scaled a)

deriving instance Generic Coercion

coercionKindRole' :: Coercion -> ((Type, Type), Role)
coercionKindRole' = first unPair . coercionKindRole

instance Eq Coercion where
  (==) = (==) `on` coercionKindRole'

instance Ord Coercion where
  compare = compare `on` coercionKindRole'

instance Mergeable Coercion where
  rootStrategy = SortedStrategy
    coercionKindRole'
    (const $ SimpleStrategy \_ value _ -> value)
