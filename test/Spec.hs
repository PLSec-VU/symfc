{-# OPTIONS_GHC -fplugin=Pantomime #-}
{-# LANGUAGE BlockArguments #-}

module Main
  ( main
  ) where

import Test.Hspec

import Pantomime
import Pantomime.BuiltIn qualified as SymFC

-- =============================================================================
-- Test Case Definitions
-- =============================================================================

-- | Peirce's Law: ((p -> q) -> p) -> p.
-- This is a classical logic tautology that is non-trivial to prove/recognize.
{-# ANN validAssertion (Theory mempty) #-}
validAssertion :: SymFC.Sym SymFC.Bool
validAssertion = do
  p <- SymFC.fresh
  q <- SymFC.fresh
  pure $ ((p `SymFC.implies` q) `SymFC.implies` p) `SymFC.implies` p

-- | Fallacy of Affirming the Consequent: ((p -> q) ∧ q) -> p.
-- This is invalid: if p is False and q is True, the premise holds but the conclusion is False.
{-# ANN invalidAssertion (Theory mempty) #-}
invalidAssertion :: SymFC.Sym SymFC.Bool
invalidAssertion = do
  p <- SymFC.fresh
  q <- SymFC.fresh
  let (&&.) = (SymFC.&&)
  pure $ ((p `SymFC.implies` q) &&. q) `SymFC.implies` p

-- =============================================================================
-- Test Suite
-- =============================================================================

main :: IO ()
main = hspec $ do
  describe "Pantomime Symbolic Checker Unit Tests" $ do
    it "verifies validAssertion (should succeed with Nothing)" $ do
      $(pantomime 'validAssertion) `shouldBe` Nothing

    it "detects invalidAssertion (should fail with Just counterexample)" $ do
      checkInvalid $(pantomime 'invalidAssertion)

-- | Assert that a counterexample was found and print it.
checkInvalid :: Maybe String -> Expectation
checkInvalid = \case
  Just ce -> do
    putStrLn ""
    putStrLn "Counterexample found:"
    putStrLn ce
    putStrLn ""
  Nothing -> expectationFailure "Expected a counterexample but assertion was valid"
