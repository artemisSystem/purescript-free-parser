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
import Data.Foldable (foldMap, oneOfMap)
import Data.Functor.Compose (Compose(..))
import Data.Newtype (un)

type FreeAltT f g = FreeAT f (Compose Array g)

liftOuter ∷ ∀ f g. Functor g ⇒ g ~> FreeAltT f g
liftOuter f = Applicative.liftOuter (Compose [ f ])

matchFree
  ∷ ∀ f g r
  . Functor g
  ⇒ (∀ x y. f x → r (x → y) → r y)
  → (∀ x. x → r x)
  → (∀ x. Array (g (r x)) → r x)
  → (FreeAltT f g ~> r)
matchFree apply' pure' natG =
  Applicative.matchFree apply' pure' (natG <<< un Compose)

runFree
  ∷ ∀ f g h
  . Functor g
  ⇒ Alternative h
  ⇒ (f ~> h)
  → (∀ x. g (h x) → h x)
  → (FreeAltT f g ~> h)
runFree natF natG = Applicative.runFree natF (oneOfMap natG <<< un Compose)

foldFree
  ∷ ∀ f g m a
  . Functor g
  ⇒ Monoid m
  ⇒ (∀ x. f x → m)
  → (g m → m)
  → (FreeAltT f g a → m)
foldFree foldF foldG = Applicative.foldFree foldF (foldMap foldG <<< un Compose)
