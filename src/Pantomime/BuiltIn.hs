{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}

-- TODO: Perhaps 'Base' would be better than 'BuiltIn', because not everything
-- here is necessarily built-in.
--
-- TODO: A lot of functions here should still get a Haskell implementation that
-- mirrors the symbolic behaviour.
-- WARNING: Helper functions should only interact with primitive data types
-- via the primitive functions that are marked as 'OPAQUE'. These primitive
-- functions are interpreted in the backend of symbolic executor. Any direct
-- unwrapping of 'Bool' will crash the execution if it is reached.
--
-- Many of the helper functions will look verbose and are written in a somewhat
-- roundabout way. This is intentional, do not change them unless you know what
-- you're doing!
module Pantomime.BuiltIn
  -- | Embeddable constraint for user interpretations.
  ( Embeddable
  , Embedding (..)
  , embedding

  -- | Symbolic variable generation.
  , Symbolic (..)
  , symbolicP

  -- | Typeclass to differentiate primitive types.
  , Primitive (..)
  , PrimitiveType (..)

  -- | Built-in literal conversion functions.
  --
  -- We need these functions for the conversion between symbolic primitives and
  -- Haskell primitives. It is expected that an embedding will tell the symbolic
  -- evaluator what to do if it encounters these functions.
  , PlatformWordSize
  , toInt#
  , toInt8#
  , toInt16#
  , toInt32#
  , toInt64#
  , fromInt#
  , fromInt8#
  , fromInt16#
  , fromInt32#
  , fromInt64#
  , toWord#
  , toWord8#
  , toWord16#
  , toWord32#
  , toWord64#
  , fromWord#
  , fromWord8#
  , fromWord16#
  , fromWord32#
  , fromWord64#
  , toInteger
  , fromInteger

  -- TODO: I guess we don't really want to expose these to users, as they are
  -- more of an implementation detail? Perhaps we could have a different module
  -- (of which we don't expect users to import it) that exports these!
  -- | Built-in comparison function of Haskell primitives.
  --
  -- These are used to implement case-splits on primitives and utilise 'fromX#'
  -- conversions in their implementation.
  , eqInt#
  , eqInt8#
  , eqInt16#
  , eqInt32#
  , eqInt64#
  , eqWord#
  , eqWord8#
  , eqWord16#
  , eqWord32#
  , eqWord64#

  -- | Operations on type-level natural numbers.
  --
  -- These mirror the original 'KnownNat' implementation up to the inner value
  -- being the builtin 'Integer' of the symbolic executor.
  , KnownNat (..)
  , natVal
  -- TODO: Why is this an ambigous import without the fully qualified path this?
  -- The other SNat pattern synonym is a qualified import...
  , SNat (Pantomime.BuiltIn.SNat)
  , (%+)
  , (%-)
  , cmpNat
  , SomeNat (..)
  , someNatVal

  -- | System Fc operations.
  , ite
  , iteIP
  , iteI8
  , iteI16
  , iteI32
  , iteI64
  , iteWP
  , iteW8
  , iteW16
  , iteW32
  , iteW64
  , tagToEnum
  , dataToTag
  , raise

  -- | Boolean operations.
  , Bool (True, False)
  , true
  , false
  , not
  , (&&)
  , (||)
  , implies
  , xor
  , iff
  , boolean

  -- | Integer operations.
  , Integer
  , i2bv
  , ineg
  , iabs
  , iadd
  , imul
  , idiv
  , imod
  , ieq
  , ineq
  , ile
  , ilt

  -- | Bit-vector operations.
  , BitVec
  , bvu2i
  , bvs2i
  , bvsize'
  , bvsize
  , bvnot
  , bvneg
  , bvand
  , bvor
  , bvxor
  , bvadd
  , bvmul
  , bvudiv
  , bvsdiv
  , bvurem
  , bvsrem
  , bvshl
  , bvlshr
  , bvashr
  , bveq
  , bvneq
  , bvule
  , bvsle
  , bvult
  , bvslt
  , bvconcat
  , bvzext
  , bvsext
  , bvselect
  , bvzresize
  , bvsresize

  -- | Array operations.
  , Array
  , aconst
  , aselect
  , astore
  , aeq
  ) where

import Control.Monad.Identity (Identity (..))
import Data.Bits qualified as Base (Bits (..))
import Data.Coerce (Coercible, coerce)
import Data.Constraint (Dict (..), HasDict (..))
import Data.Constraint.Unsafe qualified as Base (unsafeSNat)
import Data.Composition ((.:))
import Data.Constraint.Unsafe (unsafeAxiom)
import Data.Data (Proxy (..))
import Data.Hashable (Hashable (..))
import Data.Type.Ord (Compare)
import GHC.Base
  ( TYPE
  , RuntimeRep (..)
  , Int#
  , Int8#
  , Int16#
  , Int32#
  , Int64#
  , Word#
  , Word8#
  , Word16#
  , Word32#
  , Word64#
  , Type
  , WithDict (..)
  , noinline
  )
import GHC.Int
  ( Int (..)
  , Int8 (..)
  , Int16 (..)
  , Int32 (..)
  , Int64 (..)
  )
import GHC.TypeLits (OrderingI (..))
import GHC.TypeLits qualified as Base (natVal)
import GHC.TypeNats (Nat, type (+), type (-), type (<=))
import GHC.TypeNats qualified as Base (KnownNat, pattern SNat)
import GHC.Word
  ( Word (..)
  , Word8 (..)
  , Word16 (..)
  , Word32 (..)
  , Word64 (..)
  )
import Grisette
  ( SymShift (..)
  , SizedBV (..)
  , SignConversion (..)
  , BitCast (..)
  , IntN
  )
import Grisette.Internal.SymPrim.Array qualified as Grisette
import Pantomime.Util (unsafeEq)
import Pantomime.Util qualified as Util (BitVec, (%+))
import Prelude qualified as Base
import Prelude (Applicative (..), Ordering (..), Maybe (..), ($), (.))

-- Below some stubs if we ever want to make 'Embeddable' be like 'Coercible'
-- without the evidence pattern matching.
--
-- If we do go full 'Embeddable' route with a typechecker plugin: we likely want
-- to call 'solveEquality' from 'GHC.Tc.Solver.Equality' with the given
-- constraints that all runtime representations are nominally equivalent.
--
-- class PrivateEmbeddable => Embeddable (a :: k1) (b :: k2)
--
-- embed
--   :: forall {r1} {r2} (a :: TYPE r1) (b :: TYPE r2)
--    . Embeddable a b
--   => a
--   -> b
-- embed = noinline embed

-- | Unexported typeclass that has no instances.
--
-- This disallows any instance of 'Embeddable' to be defined as this typeclass
-- requirement is not exported *and* does not have an instance.
class PrivateEmbeddable

-- | Evidence of a 'Coercible' instance for different kinded types.
--
-- Example embedding of a type to a 64-bit sized bit vector. The evidence
-- provided by 'Embeddable' is generated by the symbolic evaluator via type
-- embeddings. Term embeddings can consume these instances of 'Embeddable'.
--
-- ```
-- plus64 :: forall {r} (a :: TYPE r). Embeddable a (BitVec 64) => a -> a -> a
-- plus64 = case embedding of Embedding -> coerce bvadd
-- ```
--
-- Note that only the plugin can safely generate heterogeneous coercions. They
-- are only safe under symbolic evaluation given a coherent set of embeddings.
-- Of course, a user is free to construct an instance of 'Embedding' for a
-- homogenous coercion.
--
-- Unlike 'Coercible', 'Embeddable' is not symmetric. The first type argument is
-- the source type (i.e. the type to embed) and the second type argument is the
-- destination type (i.e. the interpretation).
class PrivateEmbeddable => Embeddable (a :: k1) (b :: k2) | a -> b where
  -- | Get the 'Embedding' instance of the typeclass.
  --
  -- We expose 'embedding' as it keeps the kind arguments invisible, which is
  -- more ergonomic when using type applications.
  embedding' :: Embedding a b

-- Instance to allow resolution of embeddings with more type saturation than
-- strictly required.
instance (PrivateEmbeddable, Embeddable a b) => Embeddable (a c) (b c) where
  embedding' = case embedding @a of Embedding -> Embedding

-- | Get the 'Embedding' instance of the typeclass.
embedding
  :: forall {k1} {k2} (a :: k1) (b :: k2)
   . Embeddable a b
  => Embedding a b
embedding = embedding'

-- | Data type carrying a 'Coercible' instance for (possibly) different kinded
-- types.
--
-- See 'Embeddable' for more information regarding heterogeneous coerions.
data Embedding (a :: k1) (b :: k2) where
  Embedding :: Coercible a b => Embedding a b

-- | Identifier used for generation of 'Symbolic' values.
type Identifier = Integer

-- | Construct symbolic versions of its inhabitant.
class Symbolic a where
  -- | Construct a symbolic value.
  --
  -- The 'Identifier' should uniquely identify this symbolic value. That is,
  -- no two instances of 'symbolic' should have overlapping variables if their
  -- starting are different.
  --
  -- WARNING: The 'Identifier' should be concrete itself. This function may
  -- halt the symbolic evaluator if this is violated.
  symbolic :: Identifier -> a

instance Symbolic Bool where
  symbolic = symbolicP

instance Symbolic Integer where
  symbolic = symbolicP

instance (KnownNat n, 1 <= n) => Symbolic (BitVec n) where
  symbolic = symbolicP

instance (Primitive k, Primitive v) => Symbolic (Array k v) where
  symbolic = symbolicP

-- | Create a symbolic value for a primitive.
--
-- Prefer 'Symbolic' if possible.
--
-- WARNING: This will halt symbolic evaluation if the identifier is symbolic.
-- This will throw an error during normal evaluation, as a concrete equivalent
-- of this function does not exist.
{-# OPAQUE symbolicP #-}
symbolicP :: forall a. Primitive a => Identifier -> a
symbolicP = noinline do
  -- NOTE: The 'Primitive' typeclass is required in the interpretation of this
  -- function by the symbolic evaluator. We use it here to remove the unused
  -- constraint.
  let _ = Dict @(Primitive a)
  Base.error "no concrete version of symbolic variable generation function"

-- TODO: For now, we'll just have the platform sized as 64-bit. Not sure how
-- we would handle this correctly? Maybe with a pragma?
-- | The bit size of this platforms 'Int#' and 'Word#' primitive.
type PlatformWordSize = 64

-- | Literal construction function for built-in Haskell 'Int#' literal.
--
-- Note that this should not be used directly. Instead, this should get a user
-- interpretation that matches the representation for 'Int#' as given by the
-- user.
-- TODO: I guess the above is true for all these functions below. Perhaps we can
-- document this once and have the instances reference this?
--
-- Actually though, it would be good to have functions to switch between Haskell
-- and Pantomime types, as one would perhaps also want to use these if they
-- plan on actually using these primitives for some check.
{-# OPAQUE toInt# #-}
toInt# :: BitVec PlatformWordSize -> Int#
toInt# (BitVec bv) = let !(I# i#) = Base.fromIntegral bv in i#

{-# OPAQUE toInt8# #-}
toInt8# :: BitVec 8 -> Int8#
toInt8# (BitVec bv) = let !(I8# i#) = Base.fromIntegral bv in i#

{-# OPAQUE toInt16# #-}
toInt16# :: BitVec 16 -> Int16#
toInt16# (BitVec bv) = let !(I16# i#) = Base.fromIntegral bv in i#

{-# OPAQUE toInt32# #-}
toInt32# :: BitVec 32 -> Int32#
toInt32# (BitVec bv) = let !(I32# i#) = Base.fromIntegral bv in i#

{-# OPAQUE toInt64# #-}
toInt64# :: BitVec 64 -> Int64#
toInt64# (BitVec bv) = let !(I64# i#) = Base.fromIntegral bv in i#

{-# OPAQUE fromInt# #-}
fromInt# :: Int# -> BitVec PlatformWordSize
fromInt# i# = Base.fromIntegral $ I# i#

{-# OPAQUE fromInt8# #-}
fromInt8# :: Int8# -> BitVec 8
fromInt8# i# = Base.fromIntegral $ I8# i#

{-# OPAQUE fromInt16# #-}
fromInt16# :: Int16# -> BitVec 16
fromInt16# i# = Base.fromIntegral $ I16# i#

{-# OPAQUE fromInt32# #-}
fromInt32# :: Int32# -> BitVec 32
fromInt32# i# = Base.fromIntegral $ I32# i#

{-# OPAQUE fromInt64# #-}
fromInt64# :: Int64# -> BitVec 64
fromInt64# i# = Base.fromIntegral $ I64# i#

{-# OPAQUE toWord# #-}
toWord# :: BitVec PlatformWordSize -> Word#
toWord# (BitVec bv) = let !(W# w#) = Base.fromIntegral bv in w#

{-# OPAQUE toWord8# #-}
toWord8# :: BitVec 8 -> Word8#
toWord8# (BitVec bv) = let !(W8# w#) = Base.fromIntegral bv in w#

{-# OPAQUE toWord16# #-}
toWord16# :: BitVec 16 -> Word16#
toWord16# (BitVec bv) = let !(W16# w#) = Base.fromIntegral bv in w#

{-# OPAQUE toWord32# #-}
toWord32# :: BitVec 32 -> Word32#
toWord32# (BitVec bv) = let !(W32# w#) = Base.fromIntegral bv in w#

{-# OPAQUE toWord64# #-}
toWord64# :: BitVec 64 -> Word64#
toWord64# (BitVec bv) = let !(W64# w#) = Base.fromIntegral bv in w#

{-# OPAQUE fromWord# #-}
fromWord# :: Word# -> BitVec PlatformWordSize
fromWord# w# = Base.fromIntegral $ W# w#

{-# OPAQUE fromWord8# #-}
fromWord8# :: Word8# -> BitVec 8
fromWord8# w# = Base.fromIntegral $ W8# w#

{-# OPAQUE fromWord16# #-}
fromWord16# :: Word16# -> BitVec 16
fromWord16# w# = Base.fromIntegral $ W16# w#

{-# OPAQUE fromWord32# #-}
fromWord32# :: Word32# -> BitVec 32
fromWord32# w# = Base.fromIntegral $ W32# w#

{-# OPAQUE fromWord64# #-}
fromWord64# :: Word64# -> BitVec 64
fromWord64# w# = Base.fromIntegral $ W64# w#

{-# OPAQUE toInteger #-}
toInteger :: Integer -> Base.Integer
toInteger = coerce

-- | Convert a Haskell 'Integer' to a pantomime 'Integer'.
--
-- This function will be used to implement the 'Num' typeclass 'fromInteger'
-- for pantomime 'Integer', and as such will allow one to write their literals.
--
-- As the conversion depends on the interpretation of haskell 'Integer', we can
-- only ask a user to provide an instance for this.
{-# OPAQUE fromInteger #-}
fromInteger :: Base.Integer -> Integer
fromInteger = coerce

eqInt# :: Int# -> Int# -> Bool
eqInt# lhs rhs = bveq (fromInt# lhs) (fromInt# rhs)

eqInt8# :: Int8# -> Int8# -> Bool
eqInt8# lhs rhs = bveq (fromInt8# lhs) (fromInt8# rhs)

eqInt16# :: Int16# -> Int16# -> Bool
eqInt16# lhs rhs = bveq (fromInt16# lhs) (fromInt16# rhs)

eqInt32# :: Int32# -> Int32# -> Bool
eqInt32# lhs rhs = bveq (fromInt32# lhs) (fromInt32# rhs)

eqInt64# :: Int64# -> Int64# -> Bool
eqInt64# lhs rhs = bveq (fromInt64# lhs) (fromInt64# rhs)

eqWord# :: Word# -> Word# -> Bool
eqWord# lhs rhs = bveq (fromWord# lhs) (fromWord# rhs)

eqWord8# :: Word8# -> Word8# -> Bool
eqWord8# lhs rhs = bveq (fromWord8# lhs) (fromWord8# rhs)

eqWord16# :: Word16# -> Word16# -> Bool
eqWord16# lhs rhs = bveq (fromWord16# lhs) (fromWord16# rhs)

eqWord32# :: Word32# -> Word32# -> Bool
eqWord32# lhs rhs = bveq (fromWord32# lhs) (fromWord32# rhs)

eqWord64# :: Word64# -> Word64# -> Bool
eqWord64# lhs rhs = bveq (fromWord64# lhs) (fromWord64# rhs)

-- | 'KnownNat' constraint using Pantomime primitive 'Integer'.
class KnownNat (n :: Nat) where
  natSing :: SNat n

instance Base.KnownNat n => KnownNat n where
  natSing = do
    let i = Base.natVal @n Proxy
    UnsafeSNat @n $ fromInteger i

instance HasDict (KnownNat n) (SNat n) where
  evidence nat = withDict @(KnownNat n) nat Dict

-- | Get the 'Integer' corresponding to the 'KnownNat' constraint.
natVal :: forall n. KnownNat n => Integer
natVal = let UnsafeSNat i = natSing @n in i

-- | Singleton natural number using Pantomime primitive 'Integer'.
newtype SNat (n :: Nat) where
  UnsafeSNat :: Integer -> SNat n

-- | A explicitly bidirectional pattern synonym relating an 'SNat' to a
-- 'KnownNat' constraint.
pattern SNat :: forall n. () => KnownNat n => SNat n
pattern SNat <- (evidence -> Dict)
  where
    SNat = natSing
{-# COMPLETE SNat #-}

infixl 6 %+
(%+) :: SNat l -> SNat r -> SNat (l + r)
(%+) = coerce $ (Base.+) @Integer

infixl 6 %-
(%-) :: forall l r.  r <= l => SNat l -> SNat r -> SNat (l - r)
(%-) = do
  -- NOTE: The dictionary ensures it is safe to perform this subtraction. We use
  -- it here to avoid a redundant constraint warning.
  let _ = Dict @(r <= l)
  coerce $ (Base.-) @Integer

cmpNat :: forall l r. SNat l -> SNat r -> OrderingI l r
cmpNat SNat SNat = case Base.compare (natVal @l) (natVal @r) of
  LT | Dict <- unsafeEq @(Compare l r) @'LT -> LTI @l @r
  EQ | Dict <- unsafeEq @l @r -> EQI @l
  GT | Dict <- unsafeEq @(Compare l r) @'GT -> GTI @l @r

data SomeNat where
  SomeNat :: KnownNat n => SomeNat

someNatVal :: Integer -> Maybe SomeNat
someNatVal i = case ilt i 0 of
  True -> Nothing
  False -> Just case UnsafeSNat i of
    nat@(UnsafeSNat @n _) -> withDict @(KnownNat n) nat $ SomeNat @n

-- | Helper function to get the Haskell 'KnownNat' constraint.
--
-- WARNING: Do not export this, it uses the 'Integer' internals and is only
-- intended to implement internals for other 'OPAQUE' functions.
withKnownNat
  :: forall n rep (r :: TYPE rep)
   . KnownNat n
  => (Base.KnownNat n => r)
  -> r
withKnownNat = do
  let UnsafeSNat (Integer i) = natSing @n
  let i' = Base.unsafeSNat $ Base.fromInteger i
  withDict @(Base.KnownNat n) i'

-- | Primitive if-then-else construct.
{-# OPAQUE ite #-}
ite :: Bool -> a -> a -> a
ite (Bool scrut) tr fl = case scrut of
  Base.True -> tr
  Base.False -> fl

data IP (a :: TYPE IntRep) where
  IP :: a -> IP a

iteIP :: forall (a :: TYPE IntRep). Bool -> a -> a -> a
iteIP scrut tr fl = let !(IP value) = ite scrut (IP tr) (IP fl) in value

data I8 (a :: TYPE Int8Rep) where
  I8 :: a -> I8 a

iteI8 :: forall (a :: TYPE Int8Rep). Bool -> a -> a -> a
iteI8 scrut tr fl = let !(I8 value) = ite scrut (I8 tr) (I8 fl) in value

data I16 (a :: TYPE Int16Rep) where
  I16 :: a -> I16 a

iteI16 :: forall (a :: TYPE Int16Rep). Bool -> a -> a -> a
iteI16 scrut tr fl = let !(I16 value) = ite scrut (I16 tr) (I16 fl) in value

data I32 (a :: TYPE Int32Rep) where
  I32 :: a -> I32 a

iteI32 :: forall (a :: TYPE Int32Rep). Bool -> a -> a -> a
iteI32 scrut tr fl = let !(I32 value) = ite scrut (I32 tr) (I32 fl) in value

data I64 (a :: TYPE Int64Rep) where
  I64 :: a -> I64 a

iteI64 :: forall (a :: TYPE Int64Rep). Bool -> a -> a -> a
iteI64 scrut tr fl = let !(I64 value) = ite scrut (I64 tr) (I64 fl) in value

data WP (a :: TYPE WordRep) where
  WP :: a -> WP a

iteWP :: forall (a :: TYPE WordRep). Bool -> a -> a -> a
iteWP scrut tr fl = let !(WP value) = ite scrut (WP tr) (WP fl) in value

data W8 (a :: TYPE Word8Rep) where
  W8 :: a -> W8 a

iteW8 :: forall (a :: TYPE Word8Rep). Bool -> a -> a -> a
iteW8 scrut tr fl = let !(W8 value) = ite scrut (W8 tr) (W8 fl) in value

data W16 (a :: TYPE Word16Rep) where
  W16 :: a -> W16 a

iteW16 :: forall (a :: TYPE Word16Rep). Bool -> a -> a -> a
iteW16 scrut tr fl = let !(W16 value) = ite scrut (W16 tr) (W16 fl) in value

data W32 (a :: TYPE Word32Rep) where
  W32 :: a -> W32 a

iteW32 :: forall (a :: TYPE Word32Rep). Bool -> a -> a -> a
iteW32 scrut tr fl = let !(W32 value) = ite scrut (W32 tr) (W32 fl) in value

data W64 (a :: TYPE Word64Rep) where
  W64 :: a -> W64 a

iteW64 :: forall (a :: TYPE Word64Rep). Bool -> a -> a -> a
iteW64 scrut tr fl = let !(W64 value) = ite scrut (W64 tr) (W64 fl) in value

-- TODO: There is no real way to implement 'raise', 'tagToEnum' and 'dataToTag'
-- non-native. Maybe we could have their Haskell implementation given by a
-- plugin? For now, we can just skip it.
--
-- Another annoying thing is how we need to expose a separate 'ite' for each
-- runtime representation. Hmmm. Actually, I guess this idea would also allow
-- us to implement the other functions above no? Maybe with the exception of
-- 'tagToEnum' (for which we could probably just use unsafeCoerce on the output
-- of 'tagToEnum#'). One problem is that we would still not be able to use it
-- as an axiom for their real Haskell counterpart, as we have no way of
-- branching on which RuntimeRep is used.

-- | Tag to enumeration conversion with the intent to match 'tagToEnum#'.
--
-- WARNING: We cannot enforce that the polymorphic value is indeed an
-- enumeration, unlike the real 'tagToEnum#'. Hence, this function is incredibly
-- unsafe.
{-# OPAQUE tagToEnum #-}
tagToEnum :: forall a. BitVec PlatformWordSize -> a
tagToEnum = noinline tagToEnum

-- | Returns the index (starting at zero) of the constructor used to produce
-- the given argument.
{-# OPAQUE dataToTag #-}
dataToTag :: forall l (a :: TYPE (BoxedRep l)). a -> BitVec PlatformWordSize
dataToTag = noinline dataToTag

-- | Raise an error in the Haskell runtime.
{-# OPAQUE raise #-}
raise :: forall {l} {r} (a :: TYPE (BoxedRep l)) (b :: TYPE r). a -> b
raise = noinline raise

-- TODO: We should provide implementations for many of the common typeclasses.
-- For now, this suffices.
-- TODO: Another thing to look into is conversion between primitive types. Idk
-- if there for example is a primitive operation to convert between an boolean
-- and a single-bit bitvector.
-- | Pantomime primitive Boolean.
newtype Bool where
  Bool :: Base.Bool -> Bool

instance Base.Eq Bool where
  (==) = convert .: iff
  (/=) = convert .: xor

{-# OPAQUE true #-}
true :: Bool
true = coerce Base.True

{-# OPAQUE false #-}
false :: Bool
false = coerce Base.False

{-# OPAQUE not #-}
not :: Bool -> Bool
not = coerce Base.not

{-# OPAQUE (&&) #-}
(&&) :: Bool -> Bool -> Bool
(&&) = coerce (Base.&&)

{-# OPAQUE (||) #-}
(||) :: Bool -> Bool -> Bool
(||) = coerce (Base.||)

{-# OPAQUE implies #-}
implies :: Bool -> Bool -> Bool
implies = coerce \lhs rhs -> Base.not lhs Base.|| rhs

{-# OPAQUE xor #-}
xor :: Bool -> Bool -> Bool
xor = coerce $ (Base./=) @Base.Bool

{-# OPAQUE iff #-}
iff :: Bool -> Bool -> Bool
iff = coerce $ (Base.==) @Base.Bool

pattern True :: Bool
pattern True <- (convert -> Base.True)
  where
    True = true

pattern False :: Bool
pattern False <- (convert -> Base.False)
  where
    False = false

{-# COMPLETE True, False #-}

-- | Convert the standard Haskell Boolean to a symbolic Boolean.
{-# INLINE boolean #-}
boolean :: Base.Bool -> Bool
boolean = \case
  Base.True -> True
  Base.False -> False

-- TODO: I dislike this name. Not sure what a better alternative is.
-- | Convert a symbolic Boolean to the standard Haskell Boolean.
convert :: Bool -> Base.Bool
convert value = ite value Base.True Base.False

-- | Pantomime primitive integer.
newtype Integer where
  Integer :: Base.Integer -> Integer

instance Base.Eq Integer where
  (==) = convert .: ieq
  (/=) = convert .: ineq

instance Base.Ord Integer where
  (<=) = convert .: ile
  (<) = convert .: ilt

instance Base.Num Integer where
  (+) = iadd
  (*) = imul
  abs = iabs
  signum x = ite (ieq 0 x) 0 $ ite (ilt 0 x) (-1) 1
  negate = ineg
  fromInteger = fromInteger

{-# OPAQUE i2bv #-}
i2bv :: forall n. KnownNat n => 1 <= n => Integer -> BitVec n
i2bv (Integer x) = withKnownNat @n $ BitVec (Base.fromInteger x)

{-# OPAQUE ineg #-}
ineg :: Integer -> Integer
ineg = coerce $ Base.negate @Base.Integer

{-# OPAQUE iabs #-}
iabs :: Integer -> Integer
iabs = coerce $ Base.abs @Base.Integer

{-# OPAQUE iadd #-}
iadd :: Integer -> Integer -> Integer
iadd = coerce $ (Base.+) @Base.Integer

{-# OPAQUE imul #-}
imul :: Integer -> Integer -> Integer
imul = coerce $ (Base.*) @Base.Integer

{-# OPAQUE idiv #-}
idiv :: Integer -> Integer -> Integer
idiv = coerce $ Base.div @Base.Integer

{-# OPAQUE imod #-}
imod :: Integer -> Integer -> Integer
imod = coerce $ Base.mod @Base.Integer

{-# OPAQUE ieq #-}
ieq :: Integer -> Integer -> Bool
ieq = coerce $ (Base.==) @Base.Integer

{-# OPAQUE ineq #-}
ineq :: Integer -> Integer -> Bool
ineq = coerce $ (Base./=) @Base.Integer

{-# OPAQUE ile #-}
ile :: Integer -> Integer -> Bool
ile = coerce $ (Base.<=) @Base.Integer

{-# OPAQUE ilt #-}
ilt :: Integer -> Integer -> Bool
ilt = coerce $ (Base.<) @Base.Integer

-- | Pantomime primitive bitvector.
data BitVec (n :: Nat) where
  BitVec :: (Base.KnownNat n, 1 <= n) => Util.BitVec n -> BitVec n

type role BitVec nominal

instance Base.Eq (BitVec n) where
  (==) lhs rhs = convert $ bveq lhs rhs

instance Base.Ord (BitVec n) where
  (<=) = convert .: bvule
  (<) = convert .: bvult

instance (KnownNat n, 1 <= n) => Base.Num (BitVec n) where
  (+) = bvadd
  (*) = bvmul
  abs = Base.id
  signum value = ite (bveq value 0) 0 1
  fromInteger = i2bv . fromInteger
  negate = bvneg

instance (KnownNat n, 1 <= n) => Base.Bits (BitVec n) where
  (.&.) = bvand
  (.|.) = bvor
  xor = bvxor
  complement = bvnot
  shiftL value (I# idx#) = do
    let idx = fromInt# idx#
    bvshl value $ bvsresize idx
  shiftR value (I# idx#) = do
    let idx = fromInt# idx#
    bvlshr value $ bvsresize idx
  rotateL = Base.undefined
  rotateR = Base.undefined
  zeroBits = Base.undefined
  bit = Base.undefined
  setBit = Base.undefined
  clearBit = Base.undefined
  complementBit = Base.undefined
  testBit = Base.undefined
  bitSizeMaybe = Base.undefined
  bitSize = Base.undefined
  isSigned _ = Base.False
  popCount = Base.undefined

bvunary
  :: (Base.KnownNat n => 1 <= n => Util.BitVec n -> Util.BitVec n)
  -> BitVec n
  -> BitVec n
bvunary f (BitVec x) = BitVec $ f x

bvbinary
  :: (Base.KnownNat n => 1 <= n => Util.BitVec n -> Util.BitVec n -> Util.BitVec n)
  -> BitVec n
  -> BitVec n
  -> BitVec n
bvbinary f (BitVec x) (BitVec y) = BitVec $ f x y

bvcompare
  :: (Base.KnownNat n => 1 <= n => Util.BitVec n -> Util.BitVec n -> Base.Bool)
  -> BitVec n
  -> BitVec n
  -> Bool
bvcompare f (BitVec x) (BitVec y) = case f x y of
  Base.True -> True
  Base.False -> False

signedBin
  :: forall n
   . Base.KnownNat n => 1 <= n
  => (IntN n -> IntN n -> IntN n)
  -> Util.BitVec n
  -> Util.BitVec n
  -> Util.BitVec n
signedBin f lhs rhs = do
  let lhs' = toSigned lhs
  let rhs' = toSigned rhs
  toUnsigned $ f lhs' rhs'

signedCmp
  :: forall n
   . Base.KnownNat n
  => 1 <= n
  => (IntN n -> IntN n -> Base.Bool)
  -> Util.BitVec n
  -> Util.BitVec n
  -> Base.Bool
signedCmp f lhs rhs = do
  let lhs' = toSigned lhs
  let rhs' = toSigned rhs
  f lhs' rhs'

{-# OPAQUE bvu2i #-}
bvu2i :: forall n. BitVec n -> Integer
bvu2i (BitVec x) = Integer $ Base.toInteger x

{-# OPAQUE bvs2i #-}
bvs2i :: forall n. BitVec n -> Integer
bvs2i (BitVec x) = Integer $ Base.toInteger (bitCast @_ @(IntN n) x)

{-# OPAQUE bvsize' #-}
bvsize' :: forall n. BitVec n -> Integer
bvsize' BitVec {} = Integer $ Base.natVal @n Proxy

-- TODO: I think we can actually just implement this one directly in Pantomime.
-- I guess it is perhaps prettier than exposing the current bvsize'.
bvsize :: forall n. BitVec n -> SNat n
bvsize bv = UnsafeSNat @n $ bvsize' bv

{-# OPAQUE bvnot #-}
bvnot :: forall n. BitVec n -> BitVec n
bvnot = bvunary Base.complement

{-# OPAQUE bvneg #-}
bvneg :: forall n. BitVec n -> BitVec n
bvneg = bvunary Base.negate

{-# OPAQUE bvand #-}
bvand :: forall n. BitVec n -> BitVec n -> BitVec n
bvand = bvbinary (Base..&.)

{-# OPAQUE bvor #-}
bvor :: forall n. BitVec n -> BitVec n -> BitVec n
bvor = bvbinary (Base..|.)

{-# OPAQUE bvxor #-}
bvxor :: forall n. BitVec n -> BitVec n -> BitVec n
bvxor = bvbinary Base.xor

{-# OPAQUE bvadd #-}
bvadd :: forall n. BitVec n -> BitVec n -> BitVec n
bvadd = bvbinary (Base.+)

{-# OPAQUE bvmul #-}
bvmul :: forall n. BitVec n -> BitVec n -> BitVec n
bvmul = bvbinary (Base.*)

{-# OPAQUE bvudiv #-}
bvudiv :: forall n. BitVec n -> BitVec n -> BitVec n
bvudiv = bvbinary Base.div

{-# OPAQUE bvsdiv #-}
bvsdiv :: forall n. BitVec n -> BitVec n -> BitVec n
bvsdiv = bvbinary $ signedBin Base.div

{-# OPAQUE bvurem #-}
bvurem :: forall n. BitVec n -> BitVec n -> BitVec n
bvurem = bvbinary Base.rem

{-# OPAQUE bvsrem #-}
bvsrem :: forall n. BitVec n -> BitVec n -> BitVec n
bvsrem = bvbinary $ signedBin Base.rem

{-# OPAQUE bvshl #-}
bvshl :: forall n. BitVec n -> BitVec n -> BitVec n
bvshl = bvbinary symShift

{-# OPAQUE bvlshr #-}
bvlshr :: forall n. BitVec n -> BitVec n -> BitVec n
bvlshr = bvbinary symShiftNegated

{-# OPAQUE bvashr #-}
bvashr :: forall n. BitVec n -> BitVec n -> BitVec n
bvashr = bvbinary $ signedBin symShiftNegated

{-# OPAQUE bveq #-}
bveq :: forall n. BitVec n -> BitVec n -> Bool
bveq = bvcompare (Base.==)

{-# OPAQUE bvneq #-}
bvneq :: forall n. BitVec n -> BitVec n -> Bool
bvneq = bvcompare (Base./=)

{-# OPAQUE bvule #-}
bvule :: forall n. BitVec n -> BitVec n -> Bool
bvule = bvcompare (Base.<=)

{-# OPAQUE bvsle #-}
bvsle :: forall n. BitVec n -> BitVec n -> Bool
bvsle = bvcompare $ signedCmp (Base.<=)

{-# OPAQUE bvult #-}
bvult :: forall n. BitVec n -> BitVec n -> Bool
bvult = bvcompare (Base.<)

{-# OPAQUE bvslt #-}
bvslt :: forall n. BitVec n -> BitVec n -> Bool
bvslt = bvcompare $ signedCmp (Base.<)

{-# OPAQUE bvconcat #-}
bvconcat :: forall l r. BitVec l -> BitVec r -> BitVec (l + r)
bvconcat (BitVec lhs) (BitVec rhs) = runIdentity do
  Base.SNat @sum <- pure $ Base.SNat @l Util.%+ Base.SNat @r
  -- SAFETY: Sum of two positives is also positive.
  Dict <- pure $ unsafeAxiom @(1 <= sum)
  pure $ BitVec (sizedBVConcat lhs rhs)

{-# OPAQUE bvzext #-}
bvzext :: forall l r. KnownNat r => l <= r => BitVec l -> BitVec r
-- SAFETY: Follows from transitivity on the constraints as BitVec internally
-- carries '1 <= l'.
bvzext (BitVec x) = withKnownNat @r case unsafeAxiom @(1 <= r) of
  Dict -> BitVec $ sizedBVZext Proxy x

{-# OPAQUE bvsext #-}
bvsext :: forall l r. KnownNat r => l <= r => BitVec l -> BitVec r
-- SAFETY: Follows from transitivity on the constraints as BitVec internally
-- carries '1 <= l'.
bvsext (BitVec x) = withKnownNat @r case unsafeAxiom @(1 <= r) of
  Dict -> BitVec $ sizedBVSext Proxy x

{-# OPAQUE bvselect #-}
bvselect
  :: forall idx width n
   . KnownNat idx
  => KnownNat width
  => 1 <= width
  => idx + width <= n
  => BitVec n
  -> BitVec width
bvselect (BitVec x) = withKnownNat @idx $ withKnownNat @width do
  BitVec $ sizedBVSelect (Proxy @idx) (Proxy @width) x

bvresize
  :: forall l r
   . KnownNat r
  => 1 <= r
  => (l <= r => BitVec l -> BitVec r)
  -> BitVec l
  -> BitVec r
bvresize f x = case cmpNat (bvsize x) (SNat @r) of
  LTI -> f x
  EQI -> x
  -- SAFETY: We have l > r, so r <= l also holds!
  GTI | Dict <- unsafeAxiom @(r <= l) -> bvselect @0 @r x

bvzresize
  :: forall l r
   . KnownNat r
  => 1 <= r
  => BitVec l
  -> BitVec r
bvzresize = bvresize bvzext

bvsresize
  :: forall l r
   . KnownNat r
  => 1 <= r
  => BitVec l
  -> BitVec r
bvsresize = bvresize bvsext

-- | The type of supported primitives, which allows you to pattern match on the
-- type of such any primitive value.
--
-- I.e. this is like 'TypeRep' but closed for symbolic primitives.
data PrimitiveType a where
  BoolType
    :: PrimitiveType Bool
  IntegerType
    :: PrimitiveType Integer
  BitVecType
    :: (KnownNat n, 1 <= n)
    => PrimitiveType (BitVec n)
  ArrayType
    :: PrimitiveType k
    -> PrimitiveType v
    -> PrimitiveType (Array k v)

instance HasDict (Primitive a) (PrimitiveType a) where
  evidence = \case
    BoolType -> Dict
    IntegerType -> Dict
    BitVecType -> Dict
    ArrayType keyTy valTy -> runIdentity do
      Dict <- pure $ evidence keyTy
      Dict <- pure $ evidence valTy
      pure Dict

-- | Primitive typeclass, which allows you to reify the type of a primitive.
--
-- I.e. this is like 'Typeable' but closed for symbolic primitives.
class Primitive a where
  primitiveType :: PrimitiveType a

instance Primitive Bool where
  primitiveType = BoolType

instance Primitive Integer where
  primitiveType = IntegerType

instance (KnownNat n, 1 <= n) => Primitive (BitVec n) where
  primitiveType = BitVecType

instance (Primitive k, Primitive v) => Primitive (Array k v) where
  primitiveType = ArrayType primitiveType primitiveType

-- | Type family that captures the inner value that is wrapped in the
-- primitive's types.
type family Inner a where
  Inner Bool = Base.Bool
  Inner Integer = Base.Integer
  Inner (BitVec n) = Util.BitVec n
  Inner (Array k v) = Grisette.Array (Inner k) (Inner v)

-- | Get a 'Hashable' constraint on the inner type of primitives.
evidenceI :: forall a. Primitive a => Dict (Hashable (Inner a))
evidenceI = case primitiveType @a of
  BoolType -> Dict
  IntegerType -> Dict
  BitVecType -> Dict
  ArrayType @k @v k v -> runIdentity do
    Dict <- pure $ evidence k
    Dict <- pure $ evidenceI @k
    Dict <- pure $ evidence v
    Dict <- pure $ evidenceI @v
    pure Dict

-- | Unwrap the inner value of a primitive.
unwrap :: forall a. Primitive a => a -> Inner a
unwrap value = case primitiveType @a of
  BoolType -> let Bool inner = value in inner
  IntegerType -> let Integer inner = value in inner
  BitVecType -> let BitVec inner = value in inner
  ArrayType _ _ -> let Array inner = value in inner

-- | Wrap an inner value into a primitive.
wrap :: forall a. Primitive a => Inner a -> a
wrap inner = case primitiveType @a of
  BoolType -> Bool inner
  IntegerType -> Integer inner
  BitVecType @n -> withKnownNat @n $ BitVec inner
  ArrayType kTy vTy -> runIdentity do
    Dict <- pure $ evidence kTy
    Dict <- pure $ evidence vTy
    pure $ Array inner

-- | Symbolic array primitive.
data Array (k :: Type) (v :: Type) where
  Array
    :: (Primitive k, Primitive v)
    => Grisette.Array (Inner k) (Inner v)
    -> Array k v

-- We need nominal roles for correctness of the evaluator. Interestingly, we
-- actually cannot have representational roles here due to the underlying
-- implementation: they are already forced to be nominal. In case anything
-- changes there, we just keep these roles explicit here!
type role Array nominal nominal

instance Base.Eq (Array k v) where
  (==) = convert .: aeq

{-# OPAQUE aconst #-}
aconst :: forall k v. Primitive k => Primitive v => v -> Array k v
aconst value = do
  let inner = unwrap value
  Array @k @v $ Grisette.const inner

{-# OPAQUE aselect #-}
aselect :: forall k v. Array k v -> k -> v
aselect (Array array) key = runIdentity do
  Dict <- pure $ evidenceI @k
  let value = Grisette.select array $ unwrap key
  pure $ wrap value

{-# OPAQUE astore #-}
astore :: forall k v. Array k v -> k -> v -> Array k v
astore (Array array) key value = runIdentity do
  Dict <- pure $ evidenceI @k
  let array' = Grisette.store array (unwrap key) (unwrap value)
  pure $ Array array'

{-# OPAQUE aeq #-}
aeq :: forall k v. Array k v -> Array k v -> Bool
aeq (Array lhs) (Array rhs) = runIdentity do
  Dict <- pure $ evidenceI @k
  Dict <- pure $ evidenceI @v
  let eq = lhs Base.== rhs
  pure $ boolean eq
