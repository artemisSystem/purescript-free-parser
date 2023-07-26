module Control.Alternative.Free.Trans
  ( FreeAltT
  , liftOuter
  , matchFree
  , runFree
  , foldFree

  , module Exports
  ) where

import Prelude

import Control.Alternative (class Alternative)
import Control.Applicative.Free.Trans (FreeAT)
import Control.Applicative.Free.Trans (liftF) as Exports
import Control.Applicative.Free.Trans as Applicative
import Data.Either (Either(..))
import Data.Foldable (fold, oneOf)
import Data.Functor.Coproduct (Coproduct(..))

type FreeAltT f g = FreeAT f (Coproduct Array g)

liftOuter ∷ ∀ f g. Functor g ⇒ g ~> FreeAltT f g
liftOuter f = Applicative.liftOuter (Coproduct (Right f))

matchFree
  ∷ ∀ f g r
  . Functor g
  ⇒ (∀ x y. f x → r (x → y) → r y)
  → (∀ x y. Array (r x) → r (x → y) → r y)
  → (∀ x y. g (r x) → r (x → y) → r y)
  → (∀ x. x → r x)
  → (FreeAltT f g ~> r)
matchFree applyCis applyTransLeft applyTransRight =
  Applicative.matchFree applyCis case _ of
    Coproduct (Left array) → applyTransLeft array
    Coproduct (Right g) → applyTransRight g

runFree
  ∷ ∀ f g h
  . Functor g
  ⇒ Alternative h
  ⇒ (f ~> h)
  → (∀ x. g (h x) → h x)
  → (FreeAltT f g ~> h)
runFree natF natG = Applicative.runFree natF case _ of
  Coproduct (Left array) → oneOf array
  Coproduct (Right g) → natG g

foldFree
  ∷ ∀ f g m a
  . Functor g
  ⇒ Monoid m
  ⇒ (∀ x. f x → m)
  → (g m → m)
  → (FreeAltT f g a → m)
foldFree foldF foldG = Applicative.foldFree foldF case _ of
  Coproduct (Left array) → fold array
  Coproduct (Right g) → foldG g

