module SymFC
  ( plugin

  , SymFC (..)
  , Embeddings (..)
  ) where

import GHC.Plugins hiding (empty, (<>))

import SymFC.Embed
import SymFC.Passes

plugin :: Plugin
plugin = defaultPlugin
  { installCoreToDos = install
  , pluginRecompile = purePlugin
  , typeCheckResultAction = keepAnn
  }

install
  :: Applicative m
  => [CommandLineOption]
  -> [CoreToDo]
  -> m [CoreToDo]
install _ todo = pure $ runSymFCPass : todo
