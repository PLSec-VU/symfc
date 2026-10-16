module Effectful.Break
  ( Break
  , break
  , runBreak

  , Break'
  , break'
  , runBreak'
  ) where

import Prelude hiding (break)

import GHC.TypeLits (Symbol)

import Effectful
import Effectful.Dispatch.Dynamic (send, reinterpret)
import Effectful.Error.Dynamic (runErrorNoCallStackWith, throwError_)

-- | Default tag.
type Default = ""

-- | Early return effect.
type Break = Break' Default

-- | Return early.
break
  :: forall a b es
   . Break a :> es
  => a
  -> Eff es b
break = break' @Default

-- | Where to go to for our early return.
runBreak
  :: Eff (Break a : es) a
  -> Eff es a
runBreak = runBreak'

-- | Early return effect.
data Break' (s :: Symbol) a :: Effect where
  Break' :: forall s a b m. a -> Break' s a m b

type instance DispatchOf (Break' s a) = Dynamic

-- | Return early to the appropriately labelled runner.
break'
  :: forall s a b es
   . Break' s a :> es
  => a
  -> Eff es b
break' @s = send . Break' @s

-- | Where to go to for our early return, has a label to allow for nested
-- breaks.
runBreak'
  :: Eff (Break' s a : es) a
  -> Eff es a
runBreak' = reinterpret (runErrorNoCallStackWith pure) \_ (Break' result) -> do
  throwError_ result
