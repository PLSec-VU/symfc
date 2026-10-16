{-# LANGUAGE TemplateHaskellQuotes #-}

module SymFC.TH
  ( symFC
  ) where

import Language.Haskell.TH qualified as TH
import SymFC.Marker

symFC :: TH.Name -> TH.Q TH.Exp
symFC name = do
  let nameStr = TH.nameBase name
  pure $ TH.AppE (TH.VarE 'symFCMarker) (TH.LitE (TH.StringL nameStr))
