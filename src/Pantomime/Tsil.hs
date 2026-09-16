{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE ViewPatterns #-}

module Pantomime.Tsil
  ( Tsil (Tsil, Lin, Snoc)
  , toList
  , fromList
  ) where

import Data.Coerce (coerce)
import GHC.Generics (Generic (..))
import Grisette (Mergeable (..))

-- | A list to which we add in reverse order.
--
-- Note, this is implemented as a newtype for a standard Haskell list. We
-- introduce it to signify intent only.
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

{-# COMPLETE Lin, Snoc #-}

toList :: Tsil a -> [a]
toList (Tsil xs) = reverse xs

fromList :: [a] -> Tsil a
fromList = Tsil . reverse
