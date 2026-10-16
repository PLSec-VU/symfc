{-# LANGUAGE OverloadedStrings #-}

-- TODO: Rename to SymFC.Unify, I think it's cleaner and it also mirrors the
-- naming from GHC.
-- TODO: Add module docs.
module SymFC.Unification
  ( UnificationError (..)
  , OversaturatedError (..)
  , unifyApp
  , unifyApps
  , unifyExprs
  , resolveInstances
  , resolveInstancesWith
  , subsumeExpr
  ) where

import Control.Applicative (Alternative ((<|>)))
import Control.Error (LookupError (..))
import Control.Monad (when)
import Data.List (intersperse)
import Data.Traversable (for)
import Effectful
import Effectful.Break
import Effectful.Context
import Effectful.Error.Static
import Effectful.GHC.External (HasInstEnvs, lookupUniqueInst)
import GHC.Core.Class (Class)
import GHC.Core.FamInstEnv (FamInstEnvs, normaliseType)
import GHC.Core.InstEnv (InstEnvs, instanceDFunId, lookupUniqueInstEnv)
import GHC.Core.Map.Type (TypeMap)
import GHC.Core.Predicate (isEvVar, getClassPredTys_maybe)
import GHC.Core.Reduction (Reduction (..))
import GHC.Core.TyCo.Rep (Scaled (..), Type (..), scaledThing)
import GHC.Core.Unify (alwaysBindFun, tcMatchTy, tcUnifyTys)
import GHC.Data.Maybe (rightToMaybe, whenIsJust)
import GHC.Data.TrieMap (TrieMap (..), insertTM)
import GHC.Plugins hiding ((<>))
import GHC.Tc.Utils.TcType (substTy, tcSplitSigmaTy)
import Lens.Micro
import Lens.Micro.Extras (view)
import SymFC.Util
import Prelude hiding (break)

-- | Error to indicate unification failure.
--
-- Note that there may actually exists a unification for all the parts
-- individually. However, there doesn't exists a single mapping to unify all
-- type pairs.
newtype UnificationError = UnificationError [(Type, Type)]

instance Outputable UnificationError where
  ppr (UnificationError pairs) = do
    hang "Cannot unify the pairs of types" 2 $ ppr pairs

-- | Error to indicate oversaturation on an application.
data OversaturatedError = OversaturatedError CoreExpr [CoreExpr]

instance Outputable OversaturatedError where
  ppr (OversaturatedError fun args) = do
    -- Vertically concatenate using ($+$).
    let vcat' = foldl' @[] ($+$) empty

    -- Vertically separate with newlines in between.
    let vsep' = vcat' . intersperse ""

    -- Pretty print an expression with its type.
    let pprExpr expr =
          vcat'
            [ "::" <+> ppr (exprType expr),
              ppr expr
            ]

    -- The actual pretty print.
    vsep'
      [ hang "Function is oversaturated" 2 do
          pprExpr fun,
        hang "Given arguments" 2 do
          vsep' $ fmap pprExpr args
      ]

-- | Mapping used to track information for unification.
data Unification = Unification
  { -- | The substitution as dictated by a GHC unification.
    _substitution :: Subst,
    -- | The dictionary expressions/variables currently in-scope.
    _dictionaries :: TypeMap CoreExpr,
    -- | The quantifiers currently in use.
    _quantifiers :: DTyCoVarSet
  }

-- | An empty unification mapping.
emptyUnif :: Unification
emptyUnif =
  Unification
    { _substitution = emptySubst,
      _dictionaries = emptyTM,
      _quantifiers = emptyDVarSet
    }

-- | Lens into substitution of the 'Unification'.
substitution :: Lens' Unification Subst
substitution f unif = do
  let rebuild subst =
        Unification
          { _substitution = subst,
            _dictionaries = _dictionaries unif,
            _quantifiers = _quantifiers unif
          }
  rebuild <$> f (_substitution unif)

-- | Lens into dictionaries of the 'Unification'.
dictionaries :: Lens' Unification (TypeMap CoreExpr)
dictionaries f unif = do
  let rebuild dict =
        Unification
          { _substitution = _substitution unif,
            _dictionaries = dict,
            _quantifiers = _quantifiers unif
          }
  rebuild <$> f (_dictionaries unif)

-- | Lens into quantifiers of the 'Unification'.
quantifiers :: Lens' Unification DVarSet
quantifiers f unif = do
  let rebuild quants =
        Unification
          { _substitution = _substitution unif,
            _dictionaries = _dictionaries unif,
            _quantifiers = quants
          }
  rebuild <$> f (_quantifiers unif)

-- | A lens into the 'InScopeSet' of a 'Subst'.
scopeSubst :: Lens' Subst InScopeSet
scopeSubst f (Subst scope' ids tvs cvs) = do
  let rebuild scope'' = Subst scope'' ids tvs cvs
  rebuild <$> f scope'

-- | Lookup a dictionary identifier given a type.
--
-- This will not resolve instances. The purpose of this lookup is to not have
-- duplicate dictionary constraints in a unified expression.
lookupDict ::
  (Context Reader Unification :> es) =>
  (Context Writer Unification :> es) =>
  Type ->
  Eff es CoreExpr
lookupDict ty = runBreak do
  -- We need to use the new type for lookup in order to properly deduplicate
  -- constraints.
  unif <- get @Unification
  let ty' = substTy (unif ^. substitution) ty

  -- Early return when there already exists a mapping for this dictionary.
  let existing = lookupTM ty' $ unif ^. dictionaries
  whenIsJust existing break

  -- Create a fresh variable with the appropriate type.
  let scaled = Scaled ManyTy ty'
  fresh <- state $ substitution . scopeSubst %~~ freshId "dict" scaled

  -- Add the fresh variable to the dictionary map for future unification.
  let fresh' = Var fresh
  modify $ dictionaries %~ insertTM ty' fresh'

  -- Return the fresh variable.
  pure fresh'

-- | Multiple lookups using 'lookupDict'.
lookupDicts ::
  (Context Reader Unification :> es) =>
  (Context Writer Unification :> es) =>
  (Traversable f) =>
  f Type ->
  Eff es (f CoreExpr)
lookupDicts = traverse lookupDict

-- | Lookup the unifying type of a type variable.
--
-- This will additionally track the type variables that are used by the new,
-- unified type in the unification map.
lookupTy ::
  (Context Reader Unification :> es) =>
  (Context Writer Unification :> es) =>
  TyVar ->
  Eff es Type
lookupTy var = do
  -- Lookup the unifying type.
  unif <- get @Unification
  let ty = substTyVar (unif ^. substitution) var

  -- Extend the quantifier set if the substitution was a type variable.
  -- TODO: Shouldn't we gather all free type-variables (now we only gather the
  -- type variable if it exists at the root...)? Also, can't we inspect
  -- the substitution directly for this? This seems kind of roundabout... I
  -- guess in this way we know for sure they're used? I'd have to look into
  -- this to know what's up.
  case ty of
    TyVarTy var' -> modify $ quantifiers %~ flip extendDVarSet var'
    _ -> pure ()

  -- Return the unifying type
  pure ty

-- | Multiple lookups using 'lookupTy'.
lookupTys ::
  (Context Reader Unification :> es) =>
  (Context Writer Unification :> es) =>
  (Traversable f) =>
  f TyVar ->
  Eff es (f Type)
lookupTys = traverse lookupTy

-- | Fetches all free type variables.
--
-- The intent for this is to close expressions which we unified using
-- 'applyUnification'.
freeTyVars ::
  (Context Reader Unification :> es) =>
  Eff es [TyVar]
freeTyVars = do
  unif <- get @Unification
  pure $ unif ^. quantifiers . to dVarSetElems

-- | Fetches all free dictionary variables.
--
-- The intent for this is to close expressions which we unified using
-- 'applyUnification'.
freeDictIds ::
  (Context Reader Unification :> es) =>
  Eff es [DictId]
freeDictIds = do
  unif <- get @Unification
  let select = \case
        Var var | isEvVar var && isLocalId var -> (var :)
        _ -> id
  pure $ foldTM select (unif ^. dictionaries) []

-- | Closes an expression using a unification.
--
-- It is assumed that this expression has been first unified using the
-- 'applyUnification'.
closeExpr ::
  (Context Reader Unification :> es) =>
  CoreExpr ->
  Eff es CoreExpr
closeExpr expr = do
  tyVars <- freeTyVars
  dictIds <- freeDictIds
  pure $ mkLams (tyVars <> dictIds) expr

-- | Split the type of an expression into its components.
splitExprTy :: CoreExpr -> ([TyVar], ThetaType, Type)
splitExprTy = tcSplitSigmaTy . exprType

-- | Unify two types using 'unifyTypes'.
unifyType ::
  (Error UnificationError :> es) =>
  Type ->
  Type ->
  Eff es Unification
unifyType lhs rhs = unifyTypes [(lhs, rhs)]

-- | Unify the given types.
--
-- Creates a unification map for use in 'applyUnification'.
unifyTypes ::
  (HasCallStack) =>
  (Error UnificationError :> es) =>
  [(Type, Type)] ->
  Eff es Unification
unifyTypes tys = do
  let err = UnificationError tys
  let (lhs, rhs) = unzip tys
  subst <- failWith err $ tcUnifyTys alwaysBindFun lhs rhs
  pure $ Unification subst emptyTM emptyDVarSet

-- | Applies the unification map to the expression.
--
-- This will apply the type variables from the substitution to the expression.
-- Additionally, it will apply dictionary variables. They are tracked in the
-- 'Unification' map to avoid duplicate constraints.
--
-- The returned expression will have free variables as dictated by the
-- unification mapping. However way the expression is used, make sure to
-- eventually close the expression using 'closeExpr'.
applyUnification ::
  (Context Reader Unification :> es) =>
  (Context Writer Unification :> es) =>
  CoreExpr ->
  Eff es CoreExpr
applyUnification expr = do
  -- Split the type variables and theta type.
  let (tyVars, thetaTy, _) = splitExprTy expr

  -- Get the type arguments and lookup the dictionary variables.
  tyArgs <- lookupTys tyVars
  thetaArg <- lookupDicts thetaTy

  -- Apply the type arguments and dictionary variables
  let args = fmap Type tyArgs <> thetaArg
  pure $ mkApps expr args

-- | Multiple applications of the unification via 'applyUnification'.
applyUnifications ::
  (Context Reader Unification :> es) =>
  (Context Writer Unification :> es) =>
  (Traversable f) =>
  f CoreExpr ->
  Eff es (f CoreExpr)
applyUnifications = traverse applyUnification

-- | A single unifying application using 'unifyApps'.
unifyApp ::
  (HasCallStack) =>
  (Error UnificationError :> es) =>
  (Error OversaturatedError :> es) =>
  CoreExpr ->
  CoreArg ->
  Eff es CoreExpr
unifyApp fun arg = unifyApps fun [arg]

-- | Application that unifies polymorphic types.
--
-- This will apply the given arguments to the spine. Any type or dictionary
-- variables that occur prior any of the body type are unified and placed as
-- outer type and dictionary variables.
unifyApps ::
  (HasCallStack) =>
  (Error UnificationError :> es) =>
  (Error OversaturatedError :> es) =>
  CoreExpr ->
  [CoreArg] ->
  Eff es CoreExpr
unifyApps fun args = do
  -- Get the base types without type variables or theta type of all expressions.
  let bodyTy = view _3 . splitExprTy
  let funTy = bodyTy fun
  let argTys = bodyTy <$> args

  -- Create a unification mapping.
  -- TODO: Can we just ignore the multiplicity on this application?
  let (argTysRequired, _) = splitFunTys funTy & _1 . mapped %~ scaledThing
  let pairs = zip argTysRequired argTys
  when (length argTys > length argTysRequired) do
    throwError_ $ OversaturatedError fun args
  unif <- unifyTypes pairs

  -- Perform apply unification.
  evalContextLocal unif do
    fun' <- applyUnification fun
    args' <- applyUnifications args
    -- Apply the function to the arguments. The fresh type and dictionary
    -- variables are still free in this expression, so we close them.
    closeExpr $ mkApps fun' args'

-- | Unify two expressions.
--
-- This can be used to compare two expressions that are quantified different,
-- but are otherwise comparable.
unifyExprs ::
  (Error UnificationError :> es) =>
  CoreExpr ->
  CoreExpr ->
  Eff es (CoreExpr, CoreExpr)
unifyExprs lhs rhs = do
  -- Get the unifiable part of the type.
  let bodyTy = view _3 . splitExprTy
  let lhsTy = bodyTy lhs
  let rhsTy = bodyTy rhs

  -- Get a unification mapping.
  unif <- unifyType lhsTy rhsTy

  -- Use this unification mapping to unify the types..
  evalContextLocal unif do
    -- Perform apply unification. Note, it is important to first perform this
    -- step for both expressions, as we want to close both of them in the exact
    -- same way.
    lhs' <- applyUnification lhs
    rhs' <- applyUnification rhs

    -- Close both expressions.
    lhs'' <- closeExpr lhs'
    rhs'' <- closeExpr rhs'
    pure (lhs'', rhs'')

-- TODO: Using 'TypeMap CoreExpr' for instances is extremely fragile. It would
-- be a lot better to use InstEnv to resolve typeclasses. This goes for other
-- functions in this module as well!
subsumeExpr
  :: HasCallStack
  => Error SDoc :> es
  => FamInstEnvs
  -> InstEnvs
  -> CoreExpr
  -> Type
  -> Eff es CoreExpr
subsumeExpr fam insts expr ty = do
  -- Get the unifiable part of the type.
  let (curTv, curEv, curTy) = splitExprTy expr
  let (reqTv, reqEv, reqTy) = tcSplitSigmaTy ty

  -- Match the types and add all dictionaries we care about.
  let err = hcat
        [ "Could not match '"
        , ppr curTy
        , "' to the required type '"
        , ppr reqTy
        , "'."
        ]
  subst <- failWith @SDoc err $ tcMatchTy curTy reqTy

  -- Make evidence variables.
  let names = ("dict",) . unrestricted <$> reqEv
  let (lamEv, _) = freshIds names $ mkInScopeSetList reqTv

  -- Construct the local arguments to supply to the expression to unify.
  let argsTv = substTy subst . mkTyVarTy <$> curTv
  let dicts = foldlBy emptyTM lamEv \acc ev -> do
        insertTM @TypeMap (varType ev) ev acc

  -- Get the required typeclasses.
  argsEv <- for curEv \ev -> runBreak do
    let ev' = substTy subst ev
    let ev'' = reductionReducedType $ normaliseType fam Nominal ev'

    -- First try to find a local instance that is supplied to the function.
    whenIsJust (lookupTM ev'' dicts) $ break . Var @CoreBndr

    -- If no local instance exists, try to resolve the through the instance
    -- environment.
    let err' = hcat
          [ "Instance lookup of constraint '"
          -- NOTE: We use the constraint before type family reduction, as this
          -- error is usually easier to grasp.
          , ppr ev'
          , "' failed when subsuming expression."
          ]
    (cls, args) <- failWith err' $ getClassPredTys_maybe ev''
    (inst, targs) <- failWith err' . rightToMaybe $ do
      lookupUniqueInstEnv insts cls args
    pure $ mkTyApps (Var $ instanceDFunId inst) targs

  -- Construct the new expression.
  let open = mkApps expr $ fmap Type argsTv <> argsEv
  pure $ mkLams (reqTv <> lamEv) open

-- | Lookup a class instance in the instantiation environment.
--
-- This will return a dictionary instance as core expression.
lookupClassInst ::
  forall es.
  (HasCallStack) =>
  (Error (LookupError Type) :> es) =>
  (HasInstEnvs :> es) =>
  Type ->
  Eff es CoreExpr
lookupClassInst ty = do
  let failWith' :: Maybe a -> Eff es a
      failWith' = failWith $ LookupError ty

  -- Get the typeclass constructor of this type, if possible.
  (tyCon, tyArgs) <- failWith' $ splitTyConApp_maybe ty
  tyClass <- failWith' $ tyConClass_maybe tyCon

  -- Get the instance for this typeclass with supplied types, if possible.
  let adjustError = runErrorWith @(LookupError (Class, [Type])) \_ _ -> do
        throwError_ $ LookupError ty
  (clsInst, tys) <- adjustError $ lookupUniqueInst tyClass tyArgs

  -- Create an expression for the instance.
  let dict = Var $ instanceDFunId clsInst
  pure $ mkApps dict (Type <$> tys)

-- | Instantiate dictionaries in a core expression.
--
-- Notably, this will only instantiate if a unique option exists for the
-- instance. GHC will generally not by itself miss a resolvable instance of a
-- typeclass. Instead, this function is intended to be used together with other
-- unification-like functions in this module, as these unifications can create
-- resolvable typeclass constraints.
resolveInstances ::
  (HasInstEnvs :> es) =>
  CoreExpr ->
  Eff es CoreExpr
resolveInstances expr = do
  -- Get a mapping from constraints to instances.
  let theta = splitExprTy expr ^. _2
  results <- for theta do
    fmap rightToMaybe . runError @(LookupError Type) . lookupClassInst
  let instances = zip theta results

  -- Convert this mapping into a trie map.
  let dicts = foldlBy emptyTM instances \acc (ty, inst) -> do
        -- Alter the dictionary map if we found an instance.
        alterTM ty (inst <|>) acc

  -- Resolve the instances with this mapping.
  pure $ resolveInstancesWith dicts expr

resolveInstancesWith ::
  -- | Mapping from dictionary types to their instance.
  TypeMap CoreExpr ->
  CoreExpr ->
  CoreExpr
resolveInstancesWith dicts expr = do
  -- Set this dictionary for a unification.
  let unif = emptyUnif & dictionaries .~ dicts

  -- Apply the unification using the resolved instances and close it.
  runPureEff $ evalContextLocal unif do
    expr' <- applyUnification expr
    closeExpr expr'
