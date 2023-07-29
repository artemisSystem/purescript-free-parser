module Control.Applicative.Free
  ( FreeA
  , runFree
  , foldFree
  , module Exports
  ) where

import Prelude

import Control.Applicative.Free.Trans (FreeAT)
import Control.Applicative.Free.Trans (liftF) as Exports
import Control.Applicative.Free.Trans as Trans
import Data.Const (Const(..))
import Data.Newtype (un)

type FreeA f = FreeAT f (Const Void)

runFree ∷ ∀ f h. Applicative h ⇒ (f ~> h) → (FreeA f ~> h)
runFree natF = Trans.runFree natF (un Const >>> absurd)

foldFree ∷ ∀ f m a. Monoid m ⇒ (∀ x. f x → m) → (FreeA f a → m)
foldFree f = Trans.foldFree f (un Const >>> absurd)
