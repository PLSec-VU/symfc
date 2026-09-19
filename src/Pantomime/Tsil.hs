{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE ViewPatterns #-}

module Pantomime.Tsil
  ( Tsil (Tsil, Lin, Snoc)
  ) where

import Data.Coerce (coerce)
import GHC.Generics (Generic (..))
import GHC.IsList (IsList (..))
import Grisette (Mergeable (..))

-- | A list with an O(1) 'Snoc' operation.
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

-- TODO: I wonder if this (and the Foldable instance) should technically not
-- fold starting from the other direction?
instance Traversable Tsil where
  traverse @_ @a f xs = do
    let xs' = coerce @_ @[a] xs
    coerce <$> traverse f xs'

-- | An empty 'Tsil', i.e. the '[]'/'Nil' of a 'List'.
pattern Lin :: Tsil a
pattern Lin = Tsil []

-- | Append an element to the 'Tsil', i.e. the ':'/'Cons' operator of a 'List'.
pattern Snoc :: Tsil a -> a -> Tsil a
pattern Snoc xs x <- Tsil (x : (Tsil -> xs))
  where
    Snoc (Tsil xs) x = Tsil $ x : xs

{-# COMPLETE Lin, Snoc #-}

instance IsList (Tsil a) where
  type Item (Tsil a) = a

  toList = coerce $ reverse @a
  fromList = coerce $ reverse @a
