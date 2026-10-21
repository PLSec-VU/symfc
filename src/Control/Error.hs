{-# LANGUAGE OverloadedStrings #-}

module Control.Error
  ( LookupError (..)
  ) where

import GHC.Plugins (Outputable (..), IsDoc (..))

-- | A lookup error that states there did not exist a mapping for the given key.
newtype LookupError key = LookupError key
  deriving Show

instance Outputable key => Outputable (LookupError key) where
  ppr (LookupError key) = vcat ["Lookup error, key not found:", ppr key]
