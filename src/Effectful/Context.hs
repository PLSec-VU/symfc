{-# LANGUAGE UndecidableInstances #-}
module Effectful.Context
  ( Context (..)
  , ContextMode (..)
  , runContextLocal
  , evalContextLocal
  , execContextLocal
  , runContextShared
  , evalContextShared
  , execContextShared
  , runContextReader
  , runContextWriterLocal
  , execContextWriterLocal
  , runContextWriterShared
  , execContextWriterShared
  , get
  , gets
  , put
  , state
  , modify
  ) where

import Effectful
import Effectful.Dispatch.Dynamic
import Effectful.State.Static.Local qualified as Local
import Effectful.State.Static.Shared qualified as Shared

-- TODO: We should also make static variants for both local and shared
-- operations.

-- | A state-like effect, which permits multiple modes to operate on the same
-- underlying data.
--
-- The goal of this type is to remove glue code required when trying to use a
-- Reader effect whilst a State effect over the same type is present.
data Context (mode :: ContextMode) c :: Effect where
  Get :: Context Reader c m c
  -- ^ Fetch the current value of the context.
  Put :: c -> Context Writer c m ()
  -- ^ Set the current context to the given value.

type instance DispatchOf (Context mode c) = Dynamic

-- | Which operations the context permits.
data ContextMode where
  Reader :: ContextMode
  -- ^ The context only permits read operations.
  Writer :: ContextMode
  -- ^ The context only permits write operations.

-- | Run the Context effect with the given initial state and return the final
-- value along with the final state (via Effectful.State.Static.Local).
runContextLocal
  :: forall c a es
   . c
  -- ^ The initial state.
  -> Eff (Context Reader c : Context Writer c : es) a
  -> Eff es (a, c)
runContextLocal @c s0
  = Local.runState s0
  . interpret_ @(Context Writer c) (\(Put s) -> Local.put s)
  . interpret_ @(Context Reader c) (\Get -> Local.get)
  . inject

evalContextLocal
  :: forall c a es
   . c
  -- ^ The initial state.
  -> Eff (Context Reader c : Context Writer c : es) a
  -> Eff es a
evalContextLocal s0 = fmap fst . runContextLocal s0

execContextLocal
  :: forall c a es
   . c
  -- ^ The initial state.
  -> Eff (Context Reader c : Context Writer c : es) a
  -> Eff es c
execContextLocal s0 = fmap snd . runContextLocal s0

runContextShared
  :: forall c a es
   . c
  -- ^ The initial state.
  -> Eff (Context Reader c : Context Writer c : es) a
  -> Eff es (a, c)
runContextShared @c s0
  = Shared.runState s0
  . interpret_ @(Context Writer c) (\(Put s) -> Shared.put s)
  . interpret_ @(Context Reader c) (\Get -> Shared.get)
  . inject

evalContextShared
  :: forall c a es
   . c
  -- ^ The initial state.
  -> Eff (Context Reader c : Context Writer c : es) a
  -> Eff es a
evalContextShared s0 = fmap fst . runContextShared s0

execContextShared
  :: forall c a es
   . c
  -- ^ The initial state.
  -> Eff (Context Reader c : Context Writer c : es) a
  -> Eff es c
execContextShared s0 = fmap snd . runContextShared s0

runContextReader
  :: forall c a es
   . c
  -- ^ The initial environment.
  -> Eff (Context Reader c : es) a
  -> Eff es a
runContextReader @c s0
  = Local.evalState s0
  . interpret_ @(Context Reader c) (\Get -> Local.get)
  . inject

runContextWriterLocal
  :: forall c a es
   . c
  -- ^ The initial value.
  -> Eff (Context Writer c : es) a
  -> Eff es (a, c)
runContextWriterLocal @c s0
  = Local.runState s0
  . interpret_ @(Context Writer c) (\(Put s) -> Local.put s)
  . inject

execContextWriterLocal
  :: forall c a es
   . c
  -- ^ The initial value.
  -> Eff (Context Writer c : es) a
  -> Eff es c
execContextWriterLocal s0 = fmap snd . runContextWriterLocal s0

runContextWriterShared
  :: forall c a es
   . c
  -- ^ The initial value.
  -> Eff (Context Writer c : es) a
  -> Eff es (a, c)
runContextWriterShared @c s0
  = Local.runState s0
  . interpret_ @(Context Writer c) (\(Put s) -> Local.put s)
  . inject

execContextWriterShared
  :: forall c a es
   . c
  -- ^ The initial value.
  -> Eff (Context Writer c : es) a
  -> Eff es c
execContextWriterShared s0 = fmap snd . runContextWriterShared s0

-- | Fetch the current value of the context.
get
  :: forall c es
   . HasCallStack
  => Context Reader c :> es
  => Eff es c
get = send Get

-- | Get a function of the current context.
--
-- @'gets' f ≡ f '<$>' 'get'@
gets
  :: forall c es a
   . HasCallStack
  => Context Reader c :> es
  => (c -> a)
  -> Eff es a
gets = flip fmap get

-- | Set the current context to the given value.
put
  :: forall c es
   . HasCallStack
  => Context Writer c :> es
  => c
  -> Eff es ()
put = send . Put

-- | Apply the function to the current context and return a value.
state
  :: forall c es a
   . HasCallStack
  => Context Reader c :> es
  => Context Writer c :> es
  => (c -> (a, c))
  -> Eff es a
state @c f = do
  c <- get @c
  let (x, c') = f c
  put c'
  pure x

-- | Apply the function to the current context.
--
-- @'modify' f ≡ 'state' (\\s -> ((), f s))@
modify
  :: forall c es
   . HasCallStack
  => Context Reader c :> es
  => Context Writer c :> es
  => (c -> c)
  -> Eff es ()
modify f = state \s -> ((), f s)
