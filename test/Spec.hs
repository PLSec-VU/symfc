{-# OPTIONS_GHC -fplugin=SymFC #-}
{-# LANGUAGE BlockArguments #-}

module Main
  ( main
  ) where

import Test.Hspec

import SymFC
import SymFC.BuiltIn qualified as SymFC

-- =============================================================================
-- Test Case Definitions
-- =============================================================================

-- | Peirce's Law: ((p -> q) -> p) -> p.
-- This is a classical logic tautology that is non-trivial to prove/recognize.
{-# ANN validAssertion (SymFC mempty) #-}
validAssertion :: SymFC.Sym ()
validAssertion = do
  p <- SymFC.fresh
  q <- SymFC.fresh
  let prop = ((p `SymFC.implies` q) `SymFC.implies` p) `SymFC.implies` p
  result <- SymFC.valid prop
  case result of
    SymFC.None -> pure ()
    _ -> SymFC.halt

-- | Fallacy of Affirming the Consequent: ((p -> q) ∧ q) -> p.
-- This is invalid: if p is False and q is True, the premise holds but the conclusion is False.
{-# ANN invalidAssertion (SymFC mempty) #-}
invalidAssertion :: SymFC.Sym ()
invalidAssertion = do
  p <- SymFC.fresh
  q <- SymFC.fresh
  let (&&.) = (SymFC.&&)
  let prop = ((p `SymFC.implies` q) &&. q) `SymFC.implies` p
  result <- SymFC.valid prop
  case result of
    SymFC.None -> SymFC.halt
    _ -> pure ()

-- =============================================================================
-- Test Suite
-- =============================================================================

main :: IO ()
main = hspec $ do
  describe "SymFC Symbolic Checker Unit Tests" $ do
    pure ()
    -- it "verifies validAssertion (should succeed with Nothing)" $ do
    --   $(symFC 'validAssertion) `shouldBe` Nothing

    -- it "detects invalidAssertion (should fail with Just counterexample)" $ do
    --   checkInvalid $(symFC 'invalidAssertion)

-- | Assert that a counterexample was found and print it.
checkInvalid :: Maybe String -> Expectation
checkInvalid = \case
  Just ce -> do
    putStrLn ""
    putStrLn "Counterexample found:"
    putStrLn ce
    putStrLn ""
  Nothing -> expectationFailure "Expected a counterexample but assertion was valid"
