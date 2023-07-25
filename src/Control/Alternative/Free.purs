module Control.Alternative.Free
  ( FreeAlt
  , matchFree
  , runFree
  , foldFree
  , module Exports
  ) where

import Prelude

import Control.Alternative (class Alternative)
import Control.Alternative.Free.Trans (FreeAltT)
import Control.Alternative.Free.Trans as Trans
import Control.Applicative.Free.Trans (liftF) as Exports
import Data.Identity (Identity(..))
import Data.Newtype (un)
import Safe.Coerce (coerce)

type FreeAlt f = FreeAltT f Identity

matchFree
  ∷ ∀ f r
  . (∀ x y. f x → r (x → y) → r y)
  → (∀ x. x → r x)
  → (∀ x. Array (r x) → r x)
  → (FreeAlt f ~> r)
matchFree apply' pure' natArray =
  Trans.matchFree apply' pure' (natArray <<< coerceArray)
  where
  coerceArray ∷ ∀ x. Array (Identity x) → Array x
  coerceArray = coerce

runFree ∷ ∀ f h. Alternative h ⇒ (f ~> h) → (FreeAlt f ~> h)
runFree natF = Trans.runFree natF (un Identity)

foldFree ∷ ∀ f m a. Monoid m ⇒ (∀ x. f x → m) → (FreeAlt f a → m)
foldFree f = Trans.foldFree f (un Identity)
