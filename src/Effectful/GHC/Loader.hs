{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Effectful.GHC.Loader
  ( Loader (..)
  , getValue
  ) where

import Effectful
import Effectful.Dispatch.Dynamic (send)

import GHC.Plugins (Name, Type)

-- | Effect for loading the runtime value of a top-level binding, in the same
-- way GHC loads plugins.
data Loader :: Effect where
  GetValue :: forall a m. Name -> Type -> Loader m (Either Type a)

type instance DispatchOf Loader = Dynamic

-- | Load the value bound to the given name, which is expected to have the given
-- type.
--
-- On a type mismatch, this returns the actual type of the binding instead. The
-- caller is responsible for choosing @a@ to match the expected type.
getValue
  :: forall a es
   . Loader :> es
  => Name
  -> Type
  -> Eff es (Either Type a)
getValue name ty = send $ GetValue name ty
