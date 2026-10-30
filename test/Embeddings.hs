module Embeddings
  ( noEmbeddings
  , A (..)
  , B (..)
  , andA
  , andB
  , embeddingsA
  , embeddingsB
  ) where

import Prelude hiding (Bool, (&&))
import Data.Coerce (coerce)

import SymFC (Embeddings (..))
import SymFC.BuiltIn (Bool, Embeddable, Embedding (..), embedding, (&&))

-- | Embeddings for the checks that refer to them by name.
noEmbeddings :: Embeddings
noEmbeddings = mempty

newtype A = MkA Bool

newtype B = MkB Bool

-- | Not commutative on its own. Only its embedding makes it so.
{-# OPAQUE andA #-}
andA :: A -> A -> A
andA lhs _ = lhs

{-# OPAQUE andB #-}
andB :: B -> B -> B
andB lhs _ = lhs

andInterp :: forall a. Embeddable a Bool => a -> a -> a
andInterp @a = case embedding @a @Bool of
  Embedding -> coerce (&&)

embeddingsA :: Embeddings
embeddingsA = Embeddings
  { typeEmbeddings = [(''A, ''Bool)]
  , termEmbeddings = [('andA, 'andInterp)]
  }

embeddingsB :: Embeddings
embeddingsB = Embeddings
  { typeEmbeddings = [(''B, ''Bool)]
  , termEmbeddings = [('andB, 'andInterp)]
  }
