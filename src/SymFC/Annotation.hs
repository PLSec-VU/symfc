{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE OverloadedStrings #-}

module SymFC.Annotation
  ( Theory (..)
  ) where

import Data.Data (Data)
import SymFC.Embed (Embeddings)
import GHC.Utils.Outputable (Outputable (..), hang)

-- TODO: Not sure I like the name. This checks whether an expression whose
-- result is of type Bool is valid. That is, whether it will always return True.
data Theory where
  Theory :: Embeddings -> Theory
  deriving (Show, Data)

instance Outputable Theory where
  ppr (Theory axioms) = hang "Theory" 2 $ ppr axioms
