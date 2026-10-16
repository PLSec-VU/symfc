{-# LANGUAGE DuplicateRecordFields #-}

module SymFC
  ( plugin

  , Theory (..)
  , Embeddings (..)
  , symFC
  , symFCMarker
  , symFCNothing
  , symFCJust
  ) where

import GHC.Plugins hiding (empty, (<>))

import SymFC.Annotation
import SymFC.Embed
import SymFC.Passes
import SymFC.TH (symFC)
import SymFC.Marker


plugin :: Plugin
plugin = defaultPlugin
  { installCoreToDos = install
  , pluginRecompile = purePlugin
  }

install
  :: Applicative m
  => [CommandLineOption]
  -> [CoreToDo]
  -> m [CoreToDo]
install _ todo = do
  let validityPasses =
        [ printAndLintPass @Theory
        , checkValidityPass
        ]

  pure $ mconcat
    [ validityPasses
    , todo
    ]
