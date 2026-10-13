{-# LANGUAGE OverloadedStrings #-}

-- TODO: We should probably rename this module to 'Embed' at some point, but the
-- name is already taken by another module. Otherwise, 'Embedding' works. We'll
-- phase 'Embed' out likely at some point though, so maybe we can switch then.
module Pantomime.Axiom
  ( Embeddings (..)
  , EmbeddingsR (..)
  , TypeEmbeddingsR
  , TermEmbeddingsR
  , resolveEmbeddings
  ) where

import Prelude hiding (break)
import Language.Haskell.TH qualified as TH

import GHC.Core.InstEnv
  ( InstEnvs (..)
  , InstEnv
  , mkLocalClsInst
  , emptyInstEnv
  , extendInstEnv
  , unionInstEnv
  )
import GHC.Core.TyCo.Rep (UnivCoProvenance (..))
import GHC.Core.Unfold.Make (mkDFunUnfolding)
import GHC.Plugins
  ( TyCon (..)
  , Name
  , Id
  , CoreExpr
  , CoreProgram
  , Role (..)
  , Expr (..)
  , Var (..)
  , Type
  , MonadUnique (..)
  , OverlapFlag (..)
  , OverlapMode (..)
  , mkTyConTy
  , mkUnivCo
  , dataConWorkId
  , mkApps
  , mkAppTys
  , mkTyVarTy
  , mkVarOccFS
  , mkGReflRightCo
  , mkCastTy
  , classDataCon
  , typeKind
  , coercibleDataCon
  , generatedSrcSpan
  , setIdUnfolding
  , isTypeSynonymTyCon
  , expandTypeSynonyms
  , splitTyConAppNoView_maybe
  , unitDataConId
  )
import GHC.Types.Id.Make (mkDictFunId)
import GHC.Types.Name (mkInternalName)
import GHC.Utils.Outputable
  ( Outputable (..)
  , IsDoc (..)
  , IsLine (fsep, (<+>), text, hcat)
  , SDoc
  , hang
  , punctuate
  , comma
  , brackets
  )
import GHC.Types.SourceText (SourceText(..))

import Control.Monad ((>=>))

import Data.Data (Data)
import Data.Generics.Aliases (mkQ)
import Data.Generics.Schemes (something)
import Data.Traversable (for)

import Effectful
import Effectful.Context
import Effectful.Error.Static
import Effectful.GHC.External
  ( HasInstEnvs
  , HasFamInstEnvs
  , getInstEnvs
  , getFamInstEnvs
  )
import Effectful.GHC.TH
import Effectful.GHC.TyThing
import Effectful.GHC.Unique (HasUnique)

import Pantomime.BuiltIn (Embeddable, Embedding (..))
import Pantomime.Unification (subsumeExpr)
import Pantomime.Util (foldM')

-- TODO: This should be renamed to 'Embeddings' instead of 'Axioms'. We can
-- probably drop the 'Plugin' portion as well.
-- kinded types: something we don't care about within the evaluator. Instead,
-- we provide a custom typeclass. The comments should mirror this!
-- TODO: The text below should be updated to reflect the current state of
-- embeddings. We should at some point link the paper also.
-- | User axioms only visible to the plugin.
--
-- The kinds and types of the mapped terms should match up exactly. The
-- exception is that type-level axioms will be used to instantiate requirements
-- of 'Embeddable' on any term-level axiom.
--
-- # Example
--
-- Suppose the user has some bitvector type called 'IntN'.
--
-- > type IntN (n :: Nat) = ...
--
-- The user supplies the following mapping:
--
-- > IntN |-> BitVec
--
-- This roughly says that the user wants to use the underlying bitvector
-- representation 'BitVec'. 'BitVec' is treated as a primitive within the plugin
-- and is implemented using the respective SMT theory. A mapping between
-- non-primitive types is also allowed (or any mixing of these, use type aliases
-- for this).
--
-- Now, a user has some functions that operate on 'IntN'. These of course
-- require a mapping to the their respective operation on 'BitVec'. Before
-- anything, a user needs to ensure that **ALL** operations on 'IntN' are
-- through functions marked as 'OPAQUE' and that it's constructor is not
-- exported. This is to ensure correctness within the evaluator, as otherwise
-- representational equivalence is broken.
--
-- With this in mind, the following will illustrate how to write an
-- interpretation. Suppose we have an addition function for 'IntN' values.
--
-- > {-# OPAQUE plusIntN #-}
-- > plusIntN :: KnownNat n => IntN n -> IntN n -> IntN n
--
-- We can write an interpretation for this using the addition as provided by
-- 'BitVec'. The importance lies in using a coercion 'Coercible IntN BitVec'.
--
-- > plusInterp
-- >   :: Embeddable bv BitVec
-- >   => KnownNat n
-- >   => bv n
-- >   -> bv n
-- >   -> bv n
-- > plusInterp = case embedding @bv @BitVec of
-- >   Embedding -> coerce SMT.bvadd
--
-- Note, the where clause is only to trick Haskell into allowing the coercion
-- to appear at the top level. With this defintion in place, we supply the
-- appropriate mapping:
--
-- > plusIntN |-> plusInterp
--
-- Of course, the types for 'plusIntN' and 'plusInterp' do not match up
-- one-to-one. That is, to complete the interpretation, we supply 'plusInterp'
-- with the user-supplied coercion that 'Coercible IntN BitVec'. Afterwards, the
-- types match up and the function is a valid interpretation.
data Embeddings where
  Embeddings ::
    -- TODO: Probably want to remove the comment about fresh symbolic values
    -- once we change the interface on this.
    { typeEmbeddings :: [(TH.Name, TH.Name)]
    -- ^ Type-level embeddings.
    --
    -- Both the key and value of these mappings should be resolvable to a GHC
    -- 'Type'. One may think about this as providing an instance 'Embeddable'
    -- to the plugin between for the given types. This instance is used within
    -- the solver when constructing fresh symbolic values and when resolving
    -- instances for term-embeddings.
    -- TODO: Term axioms should allow for recursive definitions also. It
    -- probably won't be used much, but it would be good! I guess we would want
    -- a 'Bind' from GHC, but for template haskell names.
    -- Actually, the above is not really required I think: the embedding can
    -- always form a local recursive group. Will have to think about this!
    , termEmbeddings :: [(TH.Name, TH.Name)]
    -- ^ Term-level representational equivalence axioms.
    --
    -- Both the key and value of these mappings should be resolvable to 'Id'.
    -- This can be used to operate on types that have user-provided equivalence
    -- axioms via 'typeAxioms'. The types should match exactly between both
    -- 'Id's, with the exception of 'Coercible' instances that may be resolved
    -- using the 'typeAxioms'.
    --
    -- Note that this is a list because the ordering of the definitions does
    -- matter: any later definitions may use ones defined earlier. Duplicate
    -- definitions are considered an error.
    } -> Embeddings
  deriving (Show, Data)

instance Outputable Embeddings where
  ppr Embeddings { .. } = do
    let pprKV (key, value) = text (show key) <+> ":->" <+> text (show value)
    let pprKVList pairs = brackets $ fsep $ punctuate comma $ pprKV <$> pairs
    hang "Embeddings" 2 $ vcat
      [ hang "Type Embeddings:" 2 $ pprKVList typeEmbeddings
      , hang "Term Embeddings:" 2 $ pprKVList termEmbeddings
      ]

instance Semigroup Embeddings where
  (<>) l r = Embeddings
    { typeEmbeddings = typeEmbeddings l <> typeEmbeddings r
    , termEmbeddings = termEmbeddings l <> termEmbeddings r
    }

instance Monoid Embeddings where
  mempty = Embeddings
    { typeEmbeddings = mempty
    , termEmbeddings = mempty
    }

type TypeEmbeddingsR = InstEnv

-- TODO: I guess these might be better suited as CoreBind no?
type TermEmbeddingsR = [(Id, CoreExpr)]

-- TODO: I think it would be good to have type synonyms for both of these fields
-- as we use them independently as well.
-- | Fully resolved plugin axioms. These may be used as-is by the solver.
data EmbeddingsR where
  EmbeddingsR ::
    { typeEmbeddingsR :: TypeEmbeddingsR
    -- ^ Type-level axioms, mainly used to construct symbolic values.
    , termEmbeddingsR :: TermEmbeddingsR
    -- ^ Term-level axioms, these already have their 'Coercible' instances
    -- resolved by the type-axioms, where applicable.
    --
    -- This may be used to extend substitution environments.
    } -> EmbeddingsR

instance Outputable EmbeddingsR where
  ppr EmbeddingsR { .. } = hang "EmbeddingsR" 2 $ vcat
    [ hang "Type Embeddings:" 2 $ ppr typeEmbeddingsR
    , hang "Term Embeddings:" 2 $ ppr termEmbeddingsR
    ]

instance Semigroup EmbeddingsR where
  (<>) l r = EmbeddingsR
    { typeEmbeddingsR = unionInstEnv (typeEmbeddingsR l) (typeEmbeddingsR r)
    , termEmbeddingsR = termEmbeddingsR l <> termEmbeddingsR r
    }

instance Monoid EmbeddingsR where
  mempty = EmbeddingsR
    { typeEmbeddingsR = emptyInstEnv
    , termEmbeddingsR = mempty
    }

-- TODO: I guess we should change this to 'isValidHeadArg' or something. Then
-- check if there are not any quantifiers or typeclass constraints in there, as
-- these are also disallowed!
-- | Finds a type synonym in a 'Type'.
hasSynonym :: Type -> Maybe TyCon
hasSynonym = something $ mkQ Nothing \ty -> do
  case splitTyConAppNoView_maybe ty of
    Just (tc, _) | isTypeSynonymTyCon tc -> Just tc
    _ -> Nothing

-- | Expand all type synonyms from a type.
--
-- Throws an error if any type synonym still remains.
expandTypeSynonyms'
  :: HasCallStack
  => Error SDoc :> es
  => Type
  -> Eff es Type
expandTypeSynonyms' ty = do
  let ty' = expandTypeSynonyms ty
  case hasSynonym ty' of
    Just tc -> throwError_ @SDoc $ hcat
      [ "Type '"
      , ppr ty'
      , "' contains unsaturated type constructor '"
      , ppr tc
      , "' after type alias expansion."
      ]
    Nothing -> pure ()
  pure ty'

-- | Resolve user-supplied axioms in terms of Template Haskell names to their
-- internal Core representation.
--
-- Check 'PluginAxiom' for a more detailed explanation of user axioms.
--
-- In short, this function will resolve the Template Haskell names to their
-- respective TyCon, Id or CoreExpr. Afterwards, it will supply any 'Coercible'
-- instance as provided by the type-level axioms. The modified 'CoreExpr' is
-- then checked to match exactly the type of the 'Id' that maps to it to ensure
-- correctness.
--
-- Lastly, this also ensures that mappings are only made for OPAQUE functions.
-- A special case here we do allow is a NOINLINE function without an unfolding.
-- For these, we do not use any of the user-provided coercions.
resolveEmbeddings
  :: HasCallStack
  -- TODO: Adjust the opaque SDoc error!
  => Error SDoc :> es
  => Error (LookupError TH.Name) :> es
  => Error (LookupError Name) :> es
  => THNameToGHCName :> es
  => HasThings :> es
  => HasUnique :> es
  => HasInstEnvs :> es
  => HasFamInstEnvs :> es
  => Context Reader CoreProgram :> es
  => Context Reader [TyCon] :> es
  => Embeddings
  -> Eff es EmbeddingsR
resolveEmbeddings Embeddings { .. } = do
  -- Get the typeclass we want to instantiate.
  embeddable <- thNameToGhcName >=> lookupClass $ ''Embeddable
  embedding <- thNameToGhcName >=> lookupDataCon $ 'Embedding

  -- Gather the instance environment for resolution.
  typeEmbeddingsR <- foldM' emptyInstEnv typeEmbeddings \instEnv (tcL, tcR) -> do
    let lookupTyConTH = thNameToGhcName >=> lookupTyConAll
    tcL' <- lookupTyConTH tcL
    tcR' <- lookupTyConTH tcR

    -- FIXME: We should ensure that the kinds for the type match up, up to
    -- runtime representation. This latter part is hard though...

    -- TODO: There is a note in GHC that says the type variables in instance
    -- declarations should be completely fresh. I don't think the type variables
    -- on a TyCon are? If yes, this should be fine. If not, we should swap out
    -- their 'Unique'.
    -- Type variables that we will use in the instance declaration.
    let tvs = case isTypeSynonymTyCon tcL' of
          True -> tyConTyVars tcL'
          False -> []

    -- Apply the type variables to both type constructors and expand any type
    -- synonyms.
    let expand tc = do
          let ty = mkAppTys (mkTyConTy tc) $ fmap mkTyVarTy tvs
          -- TODO: Should we ensure that the expansion is actually only a
          -- newtype or data declaration? I think yes. In fact, we should also
          -- disallow quantifiers and typeclass requirements in this type!
          expandTypeSynonyms' ty
    tyL <- expand tcL'
    tyR <- expand tcR'

    -- Construct the kind coercion used to create the 'Embedding' instance.
    let prov = PluginProv "SymFC embedding (user-defined)"
    let kindL = typeKind tyL
    let kindR = typeKind tyR
    let coK = mkUnivCo prov [] Nominal kindR kindL

    -- Use the coercion to make a version of the right-hand side that has the
    -- same kind as the left-hand side.
    let tyR' = mkCastTy tyR coK

    -- Construct the type coercion that will be exposed by `Coercible`.
    let co = mkUnivCo prov [] Representational tyL tyR'

    -- Create the 'Coercible' dictionary.
    let coercibleDict = mkApps (Var $ dataConWorkId coercibleDataCon)
          [ Type kindL
          , Type tyL
          , Type tyR'
          , Coercion co
          ]

    -- Create the 'Embedding' data type.
    let embed = mkApps (Var $ dataConWorkId embedding)
          [ Type kindL
          , Type kindR
          , Type tyL
          , Type tyR
          , Type tyR'
          , Coercion coK
          , Coercion $ mkGReflRightCo Nominal tyR coK
          , coercibleDict
          ]

    -- The 'Embeddable' typeclass has a 'PrivateEmbeddable' requirement that is
    -- there just so users cannot create an instance manually. It is essentially
    -- a unit value with a different type, so we just pass in a unit as it is
    -- never used. Slightly hacky, but it works (we cannot create the instance
    -- correctly as it is not exported).
    let private = Var unitDataConId

    -- Create the 'DFunUnfolding'.
    let bndrs = []
    let dc = classDataCon embeddable
    let args = [Type kindL, Type kindR, Type tyL, Type tyR, private, embed]
    let unfolding = mkDFunUnfolding bndrs dc args

    -- Create a unique name for the embedding.
    unique <- getUniqueM
    let occ = mkVarOccFS "embedding"
    let name = mkInternalName unique occ generatedSrcSpan

    -- Construct the initial 'DFunId', without unfolding.
    let theta = [] -- No typeclass requirements in embeddings
    let tys = [kindL, kindR, tyL, tyR]
    let dfun = mkDictFunId name tvs theta embeddable tys

    -- Set the unfolding of the 'DFunId'.
    let dfun' = setIdUnfolding dfun unfolding

    -- Create the local typeclass instance.
    let overlap = OverlapFlag
          { overlapMode = NoOverlap NoSourceText
          , isSafeOverlap = False
          }
    let warn = Nothing
    let inst = mkLocalClsInst dfun' overlap tvs embeddable tys warn

    -- TODO: We should check whether the functional dependency is being upheld.
    -- We can do so with the function 'checkFundeps' from
    -- 'GHC.Tc.Instance.FunDeps'

    -- Extend the instance environment with the embedding.
    pure $ extendInstEnv instEnv inst

  -- Construct the instance environment used for subsumption.
  instEnvs <- getInstEnvs
  let instEnvs' = instEnvs
        { ie_local = unionInstEnv typeEmbeddingsR $ ie_local instEnvs
        }

  -- TODO: We should ensure that type embeddings and termAxioms do not
  -- contain duplicate definitions.

  -- Gather a binder mapping for a substitution. This will use the dictionary
  -- map to supply coercions to any Opaque values that require it.
  fam <- getFamInstEnvs
  termEmbeddingsR <- for termEmbeddings \(orig, interp) -> do
    -- Resolve the names as identifiers.
    let lookupIdTH = thNameToGhcName >=> lookupIdAll
    orig' <- lookupIdTH orig
    interp' <- lookupIdTH interp

    -- Check whether the interpretation matches.
    expr' <- subsumeExpr fam instEnvs' (Var interp') $ varType orig'

    -- Return the mapping.
    pure (orig', expr')

  -- Collect the resolved type and term mappings.
  pure EmbeddingsR
    { typeEmbeddingsR
    , termEmbeddingsR
    }
