module Pantomime.Subst
  ( Subst
  , mkEmptySubst
  , extendSubst
  , extendSubstMany
  , extendIdSubst
  , extendIdSubstMany
  , lookupIdSubst
  , substTy
  , substTyVar
  , substCo
  ) where

import Pantomime.Expr

import GHC.Core.Type qualified as GHC
import GHC.Plugins
  ( Var
  , Id
  , TyVar
  , CvSubstEnv
  , TvSubstEnv
  , IdEnv
  , InScopeSet
  , emptyInScopeSet
  , emptyVarEnv
  , isTyVar
  , isCoVar
  , isId
  , extendVarEnv
  , lookupVarEnv
  )

import Control.Monad (foldM)

import Effectful
import Effectful.Error.Static

-- | A substitution map for 'Expr'.
--
-- Note, it is strickingly similar to the GHC Substitution. The main difference
-- is the lookup for identifiers, which will look up a symbolic expression.
data Subst where
  Subst ::
    { scSubst :: InScopeSet
    , idSubst :: IdEnv (Runtime Expr)
    , tvSubst :: TvSubstEnv
    , cvSubst :: CvSubstEnv
    } -> Subst

-- | An empty substitution map.
mkEmptySubst :: Subst
mkEmptySubst = Subst
  { scSubst = emptyInScopeSet
  , idSubst = emptyVarEnv
  , tvSubst = emptyVarEnv
  , cvSubst = emptyVarEnv
  }

-- | Extend the substitution with the given mapping.
extendSubst
  :: HasCallStack
  => Error String :> es
  => Subst
  -> Var
  -> Arg
  -> Eff es Subst
extendSubst subst var arg = if
  | isTyVar var -> do
    -- Ensure that the variables are only types. Note that we force the
    -- evaluation here as type reduction should always terminate.
    ty <- forceTy arg

    -- Extend the type variable substitution.
    let tvSubst' = extendVarEnv (tvSubst subst) var ty
    pure subst { tvSubst = tvSubst' }

  | isCoVar var -> do
    -- Ensure that the variables are only types. Note that we force the
    -- evaluation here as type reduction should always terminate.
    co <- forceCo arg

    -- Extend the coercion variable substitution.
    let cvSubst' = extendVarEnv (cvSubst subst) var co
    pure subst { cvSubst = cvSubst' }

  | otherwise -> do
    -- Extend the identifier substitution.
    let idSubst' = extendVarEnv (idSubst subst) var arg
    pure subst { idSubst = idSubst' } 

-- | Extend the substitution with the given mappings.
extendSubstMany
  :: HasCallStack
  => Error String :> es
  => Foldable f
  => Subst
  -> f (Var, Arg)
  -> Eff es Subst
extendSubstMany = foldM $ uncurry . extendSubst

-- | Extend the identifier substitution with the given mapping.
extendIdSubst
  :: HasCallStack
  => Error String :> es
  => Subst
  -> Id
  -> Spine
  -> Eff es Subst
extendIdSubst subst var arg = if
  | isId var -> do
    -- Extend the identifier substitution.
    let idSubst' = extendVarEnv (idSubst subst) var arg
    pure subst { idSubst = idSubst' }
  | otherwise -> throwError @String "extendIdSubst: expected an Id variable"

-- | Extend the identifier substitution with the given mappings.
extendIdSubstMany
  :: HasCallStack
  => Error String :> es
  => Foldable f
  => Subst
  -> f (Id, Spine)
  -> Eff es Subst
extendIdSubstMany = foldM $ uncurry . extendIdSubst

-- | Lookup a variable in the current substitution environment.
lookupIdSubst
  :: Subst
  -> Id
  -> Maybe Spine
lookupIdSubst = lookupVarEnv . idSubst

-- | Substitute a Type.
substTy
  :: Subst
  -> Type
  -> Type
substTy subst ty = do
  let subst' = tyCoSubst subst
  GHC.substTy subst' ty

-- | Substitute a TyVar.
substTyVar
  :: Subst
  -> TyVar
  -> Type
substTyVar subst tv = do
  let subst' = tyCoSubst subst
  GHC.substTyVar subst' tv

-- | Substitute a Coercion.
substCo
  :: Subst
  -> Coercion
  -> Coercion
substCo subst ty = do
  let subst' = tyCoSubst subst
  GHC.substCo subst' ty

-- | Get a GHC Substitution than can be used for type and coercion substitution.
tyCoSubst :: Subst -> GHC.Subst
tyCoSubst Subst { .. } = GHC.Subst scSubst emptyVarEnv tvSubst cvSubst
