module Control.Applicative.Free
  ( FreeA
  , matchFree
  , runFree
  , foldFree
  , module Exports
  ) where

import Prelude

import Control.Applicative.Free.Trans (FreeAT)
import Control.Applicative.Free.Trans (liftF) as Exports
import Control.Applicative.Free.Trans as Trans
import Data.Identity (Identity(..))
import Data.Newtype (un)

type FreeA f = FreeAT f Identity

matchFree
  ∷ ∀ f r. (∀ x y. f x → r (x → y) → r y) → (∀ x. x → r x) → (FreeA f ~> r)
matchFree apply' pure' = Trans.matchFree apply' pure' (un Identity)

runFree ∷ ∀ f h. Applicative h ⇒ (f ~> h) → (FreeA f ~> h)
runFree natF = Trans.runFree natF (un Identity)

foldFree ∷ ∀ f m a. Monoid m ⇒ (∀ x. f x → m) → (FreeA f a → m)
foldFree f = Trans.foldFree f (un Identity)
