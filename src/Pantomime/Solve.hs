{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeApplications #-}
-- TODO: I want to remove many of these pragmas, also for the other files. Most
-- of them should just be included in the top-level flags. There also seems to
-- be a lot of obsolete stuff. Perhaps its good to first find out which flags
-- are actually used. I actually removed most of them here, but there's still
-- way too many in other files. Isn't there an 'obsolete pragma warning' or
-- something in GHC?

-- TODO: I feel like the pantomime dependencies that are used solely by the
-- final solver should go under Pantomime.Solve.X (e.g. Pantomime.Solve.Value).
-- Right now, the hierarchy is a bit too flat, which makes the project structure
-- a lot less clear. Alternatively, we can use Pantomime.Symbolic.X

module Pantomime.Solve
  ( checkValid
  , checkValid'
  , Counterexample (..)
  , counterexampleToPairs
  ) where

import GHC.Core qualified as GHC
import GHC.Core.FamInstEnv (FamInstEnvs)
import GHC.Core.InstEnv (InstEnvs)
import GHC.Types.Id.Make (nospecId)
import GHC.Generics (Generic)
import GHC.Plugins
  ( CoreProgram
  , Name
  , CoreExpr
  , Bind (..)
  , Var
  , exprType
  , vcat
  , emptyInScopeSet
  , getOccString
  , showSDocUnsafe
  , isId
  )
import GHC.Utils.Outputable
  ( Outputable (..)
  , IsLine (..)
  , SDoc
  , text
  , (<+>)
  , empty
  )

import Grisette (LogicalOp (..), EvalSym (..), Union, SymBool, onUnion)

import Control.DeepSeq (NFData (..))
import Control.Monad (foldM)

import Data.Traversable (for)

import Language.Haskell.TH qualified as TH

import Pantomime.Expr
  ( Expr (..)
  , Arg
  , Variant (..)
  , Literal (..)
  , mkApps
  , pprArg
  , runRuntime
  , throwE
  )
import Pantomime.Literal (BuiltInTyCon (..))
import Pantomime.Symbolise
import Pantomime.Subst
import Pantomime.Fresh
import Pantomime.Util (dbg, failWith)
import Pantomime.Axiom (EmbeddingsR (..))
import Pantomime.PrimOps (PrimOp)
import Pantomime.Defer (defer, withDeferrable)
import Pantomime.Binding
  ( InterfaceThings (..)
  , getInterfaceThings
  , getBuiltinTyCon
  , bindingsGHC
  )
import Pantomime.PrimOp qualified as PrimOps
import Pantomime.WHNF qualified as WHNF

import Effectful
import Effectful.Context
import Effectful.Error.Static
import Effectful.Exception (ErrorCall (..), throwIO)
import Effectful.GHC.TyThing
import Effectful.GHC.TH
import Effectful.GHC.External
import Effectful.Grisette.Solver
import Effectful.Provider
import Effectful.Prim.IORef.Strict (Prim)
import Effectful.Reader.Static (runReader)
import Effectful.State.Static.Local (evalState)

import Prelude hiding ((<>))

-- TODO: Definitely not the cleanest place to add these effects. I should look
-- into where to do this.
runBuiltInTypes
  :: Error (LookupError TH.Name) :> es
  => Error (LookupError Name) :> es
  => HasThings :> es
  => HasFamInstEnvs :> es
  => HasInstEnvs :> es
  => THNameToGHCName :> es
  => Eff (Context Reader BuiltInTyCon : Context Reader InterfaceThings : Context Reader FamInstEnvs : Context Reader InstEnvs : es) a
  -> Eff es a
runBuiltInTypes eff = do
  tys <- getBuiltinTyCon
  ids <- getInterfaceThings
  fam <- getFamInstEnvs
  env <- getInstEnvs
  runContextReader env . runContextReader fam . runContextReader ids . runContextReader tys $ eff

type SymboliseEff =
  [ Context Reader BuiltInTyCon
  , Context Reader InterfaceThings
  , Context Reader FamInstEnvs
  , Error String
  , Context Reader InstEnvs
  ]

newtype Lie a where
  Lie :: a -> Lie a
  deriving Generic

instance NFData (Lie a) where
  rnf _ = ()

construct
  :: HasCallStack
  => Context Reader BuiltInTyCon :> es
  => Context Reader InterfaceThings :> es
  => Context Reader FamInstEnvs :> es
  => Error String :> es
  => Context Reader InstEnvs :> es
  => [(Var, forall fs. PrimOp fs)]
  -> EmbeddingsR
  -> CoreProgram
  -> CoreExpr
  -- FIXME: This 'Lie' evades the check NFData constraint on 'withDeferrable'.
  -- I'm not sure how to go around this, so for now we just let it crash if it
  -- does occur.. :/
  -> Eff es (SymBool, Lie (Eff SymboliseEff [(Var, Arg)]))
construct prim EmbeddingsR { .. } program expr = inject @SymboliseEff $ withDeferrable do
  prim' <- for prim \(bndr, rhs) -> do
    rhs' <- defer rhs
    pure (bndr, rhs')

  -- Add the primitive operations to the substitution.
  subst0 <- extendIdSubstMany mkEmptySubst prim'

  -- Add the term bindings to the substitution.
  let termAxiomsR' = uncurry NonRec <$> termEmbeddingsR
  subst1 <- symboliseBindMany subst0 termAxiomsR'

  -- TODO: I think there is an ordering problem here between user
  -- mappings and program definitions. I guess user mappings should
  -- go first? The problem is that we don't want local definitions to
  -- overwrite them. I guess for now, we can keep the ordering like this,
  -- but this essentially restricts mappings to be used only outside of
  -- their defining module. Not the worst thing though, as the functions
  -- should truly be opaque outside of the defining module and they cannot
  -- be guaranteed to not be misused within the module.
  subst <- symboliseBindMany subst1 program

  -- Create fresh arguments.
  let ty = exprType expr
  (args, _scope) <- freshArgs typeEmbeddingsR (collectValBinders expr) ty emptyInScopeSet

  result <- defer do
    fun <- symbolise subst expr
    res <- mkApps fun $ fmap snd args
    case res of
      Lit (Bool value) -> pure value
      _ -> throwE @String "Result of symbolic evaluation is not a Boolean literal"

  -- TODO: What to do about raise? Do we really just want to return false? I
  -- guess for now it is fine.
  let eq = flip (onUnion @Union) (runRuntime result) \case
        Left Unreachable -> true
        Left UB -> false
        Left Raise {} -> false
        Right value -> value
  pure (eq, Lie $ pure args)

newtype Counterexample = Counterexample
  { counterexampleBindings :: [(String, String)]
  }

-- | Formats a counterexample into a list of name-value string pairs.
counterexampleToPairs :: Counterexample -> [(String, String)]
counterexampleToPairs = counterexampleBindings

instance Outputable Counterexample where
  ppr (Counterexample bindings) = pprBindings bindings
    where
      pprBindings [] = empty
      pprBindings ((name, val) : rest) = vcat
        [ "==================="
        , text name <+> "=" <+> text val
        , pprBindings rest
        ]

checkValid'
  :: forall es
   . HasCallStack
  => Error SDoc :> es
  => Error (LookupError TH.Name) :> es
  => Error (LookupError Name) :> es
  => Context Reader CoreProgram :> es
  => Prim :> es
  => HasThings :> es
  => THNameToGHCName :> es
  => EmbeddingsR
  -> Var
  -> Eff es (Maybe Counterexample)
checkValid' EmbeddingsR { .. } var = do
  -- Construct the initial global environment, which contains the embeddings.
  let terms = uncurry NonRec <$> termEmbeddingsR
  global <- foldM WHNF.extendBind WHNF.emptyEnv terms

  -- Create the full environment runner for the evaluator.
  prims <- PrimOps.resolve
  let runner = evalState global . runReader prims

  -- Create the local substitution environment.
  program <- get @CoreProgram
  env <- foldM WHNF.extendBind WHNF.emptyEnv program

  -- Get a thunk corresponding to the variable.
  let err = "Variable not in local program '" <> ppr var <> "'"
  thunk <- failWith @SDoc err $ WHNF.lookup env var

  -- Force the thunk.
  whnf <- runner $ WHNF.force thunk

  dbg whnf
  throwError_ @SDoc "End of test!"

checkValid
  :: forall es
   . HasCallStack
  => Error String :> es
  => Error (LookupError TH.Name) :> es
  => Error (LookupError Name) :> es
  => Error SolverError :> es
  => Context Reader CoreProgram :> es
  => HasInstEnvs :> es
  => HasThings :> es
  => THNameToGHCName :> es
  => HasFamInstEnvs :> es
  => Provider_ Solver () :> es
  => EmbeddingsR
  -> CoreExpr
  -> Eff es (Maybe Counterexample)
checkValid axioms expr = runBuiltInTypes do
  -- TODO: Somehow this code doesn't read very nice. I think I should review it.
  program <- get @CoreProgram

  prim <- bindingsGHC

  -- TODO: Is there perhaps a better place to add this? Ideally we just do it
  -- as a normal axiom, but I cannot find where 'nospec' is defined...
  idId <- thNameToGhcName 'id >>= lookupIdAll
  let axioms' = axioms { termEmbeddingsR = (nospecId, GHC.Var idId) : termEmbeddingsR axioms } 

  (eq, Lie args) <- construct prim axioms' program expr

  solution <- provide_ @Solver $ solve (symNot eq)

  -- TODO: Do we not have to assert that the input is never Invalid?
  -- I.e. if we want to prove equivalence between (assuming inputs cannot be
  -- bottom):
  --
  -- ex1 :: Void -> Int
  -- ex1 _ = 0
  --
  -- ex2 :: Void -> Int
  -- ex2 _ = 1
  --
  -- Then we need to pass in the constraint that Void only contains Invalid
  -- as a value.
  --
  -- I guess the expected behaviour in these cases would be that the function
  -- forces the Void value in order to create any value via an empty case. I
  -- don't think in practise we care about this one.
  --
  -- In fact, if the user doesn't force it, it is indeed not the case that these
  -- functions are equivalent.
  case solution of
    Satisfiable model -> do
      -- TODO: I should probably check whether the arguments are recursive
      -- before printing? Alternatively, I could just have a maximum depth.
      args' <- inject args
      let bindings = flip map args' \(bndr, arg) ->
            let arg' = evalSym True model arg
                name = getOccString bndr
                value = showSDocUnsafe (pprArg id arg')
            in (name, value)
      pure $ Just (Counterexample bindings)
    Unsatisfiable -> do
      dbg @SDoc "Expression was valid!"
      pure Nothing
    -- FIXME: I don't think this is always true. e.g. not sure about some of the
    -- floating point stuff for example.
    Unknown -> throwIO $ ErrorCall "checks are in decidable fragment"

collectValBinders :: CoreExpr -> [String]
collectValBinders expr = go expr
  where
    go (GHC.Lam b e)
      | isId b    = getOccString b : go e
      | otherwise = go e
    go (GHC.Tick _ e) = go e
    go (GHC.Cast e _) = go e
    go (GHC.Let _ e)  = go e
    go _ = []
