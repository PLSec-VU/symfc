{-# LANGUAGE MagicHash #-}

-- | Module defining the symbolic primitives and helper functions.
module Pantomime.PrimOp
  -- | Primitive operations and its functions.
  ( PrimOp (..)
  , arity
  , bindings
  ) where

import GHC.Plugins (Arity, Outputable (ppr))
import GHC.Generics (Generic)
import Grisette (Mergeable, Default (..))
import Language.Haskell.TH qualified as TH
import Pantomime.BuiltIn qualified as Builtin
import Prelude hiding (lookup)
import Unsafe.Coerce qualified as Builtin (unsafeEqualityProof)

-- | The primitive operations supported by the symbolic evaluator.
data PrimOp where
  -- System FC operations.
  IteOp :: PrimOp
  TagToEnumOp :: PrimOp
  DataToTagOp :: PrimOp
  RaiseOp :: PrimOp
  UnsafeEqualityProofOp :: PrimOp

  -- Symbolic variable operations.
  SymbolicPrimOp :: PrimOp

  -- Boolean operations.
  TrueOp :: PrimOp
  FalseOp :: PrimOp
  NotOp :: PrimOp
  ImpliesOp :: PrimOp
  AndOp :: PrimOp
  OrOp :: PrimOp
  IffOp :: PrimOp
  XorOp :: PrimOp

  -- Integer operations.
  IntToBitVecOp :: PrimOp
  IntNegOp :: PrimOp
  IntAbsOp :: PrimOp
  IntAddOp :: PrimOp
  IntMulOp :: PrimOp
  IntDivOp :: PrimOp
  IntModOp :: PrimOp
  IntEqOp :: PrimOp
  IntNeqOp :: PrimOp
  IntLeOp :: PrimOp
  IntLtOp :: PrimOp

  -- Bitvector operations.
  BitVecUToIntOp :: PrimOp
  BitVecSToIntOp :: PrimOp
  BitVecSizeOp :: PrimOp
  BitVecNotOp :: PrimOp
  BitVecNegOp :: PrimOp
  BitVecAndOp :: PrimOp
  BitVecOrOp :: PrimOp
  BitVecXorOp :: PrimOp
  BitVecAddOp :: PrimOp
  BitVecMulOp :: PrimOp
  BitVecUDivOp :: PrimOp
  BitVecSDivOp :: PrimOp
  BitVecURemOp :: PrimOp
  BitVecSRemOp :: PrimOp
  BitVecShl :: PrimOp
  BitVecLShr :: PrimOp
  BitVecAShr :: PrimOp
  BitVecEqOp :: PrimOp
  BitVecNeqOp :: PrimOp
  BitVecULeOp :: PrimOp
  BitVecSLeOp :: PrimOp
  BitVecULtOp :: PrimOp
  BitVecSLtOp :: PrimOp
  BitVecConcatOp :: PrimOp
  BitVecZExtOp :: PrimOp
  BitVecSExtOp :: PrimOp
  BitVecSelectOp :: PrimOp

  -- Array operations.
  ArrayConstOp :: PrimOp
  ArraySelectOp :: PrimOp
  ArrayStoreOp :: PrimOp
  ArrayEqOp :: PrimOp
  deriving Generic
  deriving Mergeable via Default PrimOp

instance Outputable PrimOp where
  ppr = \case
    IteOp -> "ite"
    TagToEnumOp -> "tagToEnum"
    DataToTagOp -> "dataToTag"
    RaiseOp -> "raise"
    UnsafeEqualityProofOp -> "unsafeEqualityProof"
    SymbolicPrimOp -> "symbolicP"
    TrueOp -> "true"
    FalseOp -> "false"
    NotOp -> "not"
    ImpliesOp -> "implies"
    AndOp -> "and"
    OrOp -> "or"
    IffOp -> "iff"
    XorOp -> "xor"
    IntToBitVecOp -> "i2bv"
    IntNegOp -> "ineg"
    IntAbsOp -> "iabs"
    IntAddOp -> "iadd"
    IntMulOp -> "imul"
    IntDivOp -> "idiv"
    IntModOp -> "imod"
    IntEqOp -> "ieq"
    IntNeqOp -> "ineq"
    IntLeOp -> "ile"
    IntLtOp -> "ilt"
    BitVecUToIntOp -> "bvu2i"
    BitVecSToIntOp -> "bvs2i"
    BitVecSizeOp -> "bvsize"
    BitVecNotOp -> "bvnot"
    BitVecNegOp -> "bvneg"
    BitVecAndOp -> "bvand"
    BitVecOrOp -> "bvor"
    BitVecXorOp -> "bvxor"
    BitVecAddOp -> "bvadd"
    BitVecMulOp -> "bvmul"
    BitVecUDivOp -> "bvudiv"
    BitVecSDivOp -> "bvsdiv"
    BitVecURemOp -> "bvurem"
    BitVecSRemOp -> "bvsrem"
    BitVecShl -> "bvshl"
    BitVecLShr -> "bvlshr"
    BitVecAShr -> "bvashr"
    BitVecEqOp -> "bveq"
    BitVecNeqOp -> "bvneq"
    BitVecULeOp -> "bvule"
    BitVecSLeOp -> "bvsle"
    BitVecULtOp -> "bvult"
    BitVecSLtOp -> "bvslt"
    BitVecConcatOp -> "bvconcat"
    BitVecZExtOp -> "bvzext"
    BitVecSExtOp -> "bvsext"
    BitVecSelectOp -> "bvselect"
    ArrayConstOp -> "aconst"
    ArraySelectOp -> "aselect"
    ArrayStoreOp -> "astore"
    ArrayEqOp -> "aeq"

-- TODO: It would probably be better to get the arity information from the type.
-- We can move the primitive type definition to this module (or into its own
-- module) and instead make a giant case to fetch the type. Then we can compute
-- the arity from that type.
-- | Get the 'Arity' of the given primitive operation.
arity :: PrimOp -> Arity
arity = \case
  IteOp -> 3
  TagToEnumOp -> 2
  DataToTagOp -> 1
  RaiseOp -> 1
  UnsafeEqualityProofOp -> 0
  SymbolicPrimOp -> 2
  TrueOp -> 0
  FalseOp -> 0
  NotOp -> 1
  ImpliesOp -> 2
  AndOp -> 2
  OrOp -> 2
  IffOp -> 2
  XorOp -> 2
  IntToBitVecOp -> 3
  IntNegOp -> 1
  IntAbsOp -> 1
  IntAddOp -> 2
  IntMulOp -> 2
  IntDivOp -> 2
  IntModOp -> 2
  IntEqOp -> 2
  IntNeqOp -> 2
  IntLeOp -> 2
  IntLtOp -> 2
  BitVecUToIntOp -> 1
  BitVecSToIntOp -> 1
  BitVecSizeOp -> 1
  BitVecNotOp -> 1
  BitVecNegOp -> 1
  BitVecAndOp -> 2
  BitVecOrOp -> 2
  BitVecXorOp -> 2
  BitVecAddOp -> 2
  BitVecMulOp -> 2
  BitVecUDivOp -> 2
  BitVecSDivOp -> 2
  BitVecURemOp -> 2
  BitVecSRemOp -> 2
  BitVecShl -> 2
  BitVecLShr -> 2
  BitVecAShr -> 2
  BitVecEqOp -> 2
  BitVecNeqOp -> 2
  BitVecULeOp -> 2
  BitVecSLeOp -> 2
  BitVecULtOp -> 2
  BitVecSLtOp -> 2
  BitVecConcatOp -> 2
  BitVecZExtOp -> 3
  BitVecSExtOp -> 3
  BitVecSelectOp -> 5
  ArrayConstOp -> 3
  ArraySelectOp -> 2
  ArrayStoreOp -> 3
  ArrayEqOp -> 2

-- | A mapping from 'TH.Name' name to 'PrimOp'.
bindings :: [(TH.Name, PrimOp)]
bindings =
  -- System FC bindings.
  ----------------------
  [ ('Builtin.ite, IteOp)
  , ('Builtin.tagToEnum, TagToEnumOp)
  , ('Builtin.dataToTag, DataToTagOp)
  , ('Builtin.raise, RaiseOp)
  -- TODO: This one directly binds the Haskell unsafe equality proof. I guess
  -- this is really the only sensible binding, but it would be nicest to expose
  -- our own and then use the embeddings to bind it (of course, this should be
  -- added to the standard library embeddings by default).
  , ('Builtin.unsafeEqualityProof, UnsafeEqualityProofOp)

  -- Symbolic variable generation.
  --------------------------------
  , ('Builtin.symbolic#, SymbolicPrimOp)

  -- Boolean bindings.
  --------------------
  , ('Builtin.true, TrueOp)
  , ('Builtin.false, FalseOp)
  , ('Builtin.not, NotOp)
  , ('(Builtin.&&), AndOp)
  , ('(Builtin.||), OrOp)
  , ('Builtin.implies, ImpliesOp)
  , ('Builtin.xor, XorOp)
  , ('Builtin.iff, IffOp)

  -- Integer bindings.
  --------------------
  , ('Builtin.i2bv, IntToBitVecOp)
  , ('Builtin.ineg, IntNegOp)
  , ('Builtin.iabs, IntAbsOp)
  , ('Builtin.iadd, IntAddOp)
  , ('Builtin.imul, IntMulOp)
  , ('Builtin.idiv, IntDivOp)
  , ('Builtin.imod, IntModOp)
  , ('Builtin.ieq, IntEqOp)
  , ('Builtin.ineq, IntNeqOp)
  , ('Builtin.ile, IntLeOp)
  , ('Builtin.ilt, IntLtOp)

  -- Bitvector bindings.
  ----------------------
  , ('Builtin.bvu2i, BitVecUToIntOp)
  , ('Builtin.bvs2i, BitVecSToIntOp)
  , ('Builtin.bvsize', BitVecSizeOp)
  , ('Builtin.bvnot, BitVecNotOp)
  , ('Builtin.bvneg, BitVecNegOp)
  , ('Builtin.bvand, BitVecAndOp)
  , ('Builtin.bvor, BitVecOrOp)
  , ('Builtin.bvxor, BitVecXorOp)
  , ('Builtin.bvadd, BitVecAddOp)
  , ('Builtin.bvmul, BitVecMulOp)
  , ('Builtin.bvudiv, BitVecUDivOp)
  , ('Builtin.bvsdiv, BitVecSDivOp)
  , ('Builtin.bvurem, BitVecURemOp)
  , ('Builtin.bvsrem, BitVecSRemOp)
  , ('Builtin.bvshl, BitVecShl)
  , ('Builtin.bvlshr, BitVecLShr)
  , ('Builtin.bvashr, BitVecAShr)
  , ('Builtin.bveq, BitVecEqOp)
  , ('Builtin.bvneq, BitVecNeqOp)
  , ('Builtin.bvule, BitVecULeOp)
  , ('Builtin.bvsle, BitVecSLeOp)
  , ('Builtin.bvult, BitVecULtOp)
  , ('Builtin.bvslt, BitVecSLtOp)
  , ('Builtin.bvconcat, BitVecConcatOp)
  , ('Builtin.bvzext, BitVecZExtOp)
  , ('Builtin.bvsext, BitVecSExtOp)
  , ('Builtin.bvselect, BitVecSelectOp)

  -- Array bindings.
  ------------------
  , ('Builtin.aconst, ArrayConstOp)
  , ('Builtin.aselect, ArraySelectOp)
  , ('Builtin.astore, ArrayStoreOp)
  , ('Builtin.aeq, ArrayEqOp)
  ]
