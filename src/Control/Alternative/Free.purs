module Control.Alternative.Free
  ( FreeAlt
  , runFree
  , foldFree
  , module Exports
  ) where

import Prelude

import Control.Alternative (class Alternative)
import Control.Alternative.Free.Trans (FreeAltT)
import Control.Alternative.Free.Trans as Trans
import Control.Applicative.Free.Trans (liftF) as Exports
import Data.Const (Const(..))
import Data.Newtype (un)

type FreeAlt f = FreeAltT f (Const Void)

runFree ∷ ∀ f h. Alternative h ⇒ (f ~> h) → (FreeAlt f ~> h)
runFree natF = Trans.runFree natF (un Const >>> absurd)

foldFree ∷ ∀ f m a. Monoid m ⇒ (∀ x. f x → m) → (FreeAlt f a → m)
foldFree f = Trans.foldFree f (un Const >>> absurd)
