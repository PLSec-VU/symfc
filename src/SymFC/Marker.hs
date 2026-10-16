module SymFC.Marker
  ( symFCMarker
  , symFCNothing
  , symFCJust
  ) where

symFCMarker :: String -> Maybe String
symFCMarker name = error $
  "The marker function 'symFCMarker' for '" ++ name ++ "' was not replaced by the GHC compiler plugin pass."
{-# NOINLINE symFCMarker #-}

symFCNothing :: Maybe String
symFCNothing = Nothing
{-# NOINLINE symFCNothing #-}

symFCJust :: String -> Maybe String
symFCJust x = Just x
{-# NOINLINE symFCJust #-}
