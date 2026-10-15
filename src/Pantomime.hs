{-# LANGUAGE DuplicateRecordFields #-}

module Pantomime
  ( plugin

  , Theory (..)
  , Embeddings (..)
  , pantomime
  , pantomimeMarker
  , pantomimeNothing
  , pantomimeJust
  ) where

import GHC.Plugins hiding (empty, (<>))

import Pantomime.Annotation
import Pantomime.Embed
import Pantomime.Passes
import Pantomime.TH (pantomime)
import Pantomime.Marker


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
