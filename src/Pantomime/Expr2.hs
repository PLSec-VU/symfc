module Pantomime.Expr2
  ( Expr
  , ExprF
  , TermF (..)
  , Alt (..)
  , Runtime
  , Bottom (..)
  , translate
  ) where

import Control.Monad.Except (ExceptT)
import Data.Coerce (coerce)
import Data.Composition ((.:))
import Data.Fix (Fix (..))
import Data.Functor.Foldable (Base)
import Effectful (Eff, type (:>))
import Effectful.Error.Static (Error, HasCallStack)
import GHC.Core qualified as GHC
import GHC.Generics ((:.:) (..))
import GHC.Plugins (Id, Var, Type, AltCon, CoercionR, Coercion, SDoc)
import Grisette (Union)
import Pantomime.Literal (Literal)

type Expr = Fix ExprF

type ExprF = Runtime :.: TermF

type instance Base Expr = ExprF

data TermF a where
  Var :: Id -> TermF a
  Lit :: Literal -> TermF a
  App :: a -> a -> TermF a
  Lam :: Var -> a -> TermF a
  -- Rec :: [(Var, a)] -> TermF a
  Case :: a -> Var -> Type -> [Alt a] -> TermF a
  Cast :: a -> CoercionR -> TermF a
  Type :: Type -> TermF a
  Coercion :: Coercion -> TermF a

-- TODO: 'AltCon' is not the correct fit, as it doesn't match the literals of
-- the symbolic evaluator.
data Alt a where
  Alt :: AltCon -> [Var] -> a -> Alt a

type Runtime = ExceptT Bottom Union

data Bottom where
  Diverge :: Bottom
  Unreachable :: Bottom
  UndefinedBehaviour :: Bottom
  Raise :: Expr -> Bottom

mkVar :: Var -> Expr
mkVar = coerce $ pure @Runtime . Var

mkLit :: Literal -> Expr
mkLit = coerce $ pure @Runtime . Lit

mkApp :: Expr -> Expr -> Expr
mkApp = coerce $ pure @Runtime .: App

mkCast :: Expr -> CoercionR -> Expr
mkCast = coerce $ pure @Runtime .: Cast

mkType :: Type -> Expr
mkType = coerce $ pure @Runtime . Type

mkCoercion :: Coercion -> Expr
mkCoercion = coerce $ pure @Runtime . Coercion

translate
  :: HasCallStack
  => Error SDoc :> es
  => GHC.CoreExpr
  -> Eff es Expr
translate = \case
  GHC.Var var -> pure $ mkVar var
  GHC.Lit lit -> undefined
  GHC.App fun arg -> do
    fun' <- translate fun
    arg' <- translate arg
    pure $ mkApp fun' arg'
  GHC.Lam bndr body -> do
    body' <- translate body
    pure $ mkLam bndr body'
  GHC.Let bind body -> undefined
  GHC.Case scrut bndr ty alts -> undefined
  GHC.Cast body co -> do
    body' <- translate body
    pure $ mkCast body' co
  GHC.Tick _tick body -> translate body
  GHC.Type ty -> pure $ mkType ty
  GHC.Coercion co -> pure $ mkCoercion co
