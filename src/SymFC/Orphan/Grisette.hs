{-# OPTIONS_GHC -Wno-orphans #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}

module SymFC.Orphan.Grisette
  ( pattern Single
  , pattern If
  ) where

import Grisette
  ( Union
  , UnionView (..)
  , IfViewResult (..)
  , SymBranching (..)
  , SymBool
  )

-- | Pattern match to extract single values with 'singleView'.
--
-- >>> case (return 1 :: Union Integer) of Single v -> v
-- 1
pattern Single
  :: UnionView u
  => a
  -> u a
pattern Single x <- (singleView -> Just x)
  where
    Single x = pure x

-- | Pattern match to extract guard values with 'ifView'
--
-- >>> case (mrgIfPropagatedStrategy "a" (return 1) (return 2) :: Union Integer) of If c t f -> (c,t,f)
-- (a,<1>,<2>)
pattern If
  :: UnionView u
  => SymBranching u
  => SymBool
  -> u a
  -> u a
  -> u a
pattern If c t f <- (ifView -> Just (IfViewResult c t f))
  where
    If c t f = mrgIfPropagatedStrategy c t f

-- | NOTE: We define our own version of 'Single' and 'If' as we specifically do
-- not want the 'Mergeable' constraint that Grisette imposes.
{-# COMPLETE Single, If #-}

-- TODO: We should create a merge request for these. Having them as orphans
-- doesn't really make sense.
instance Foldable Union where
  foldr f = go
    where
      go acc = \case
        Single value -> f value acc
        If _ true false -> go (go acc false) true

instance Traversable Union where
  traverse f = go
    where
      go = \case
        Single value -> pure <$> f value
        If scrut true false -> do
          mrgIfPropagatedStrategy scrut <$> go true <*> go false
