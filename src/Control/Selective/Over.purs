module Control.Selective.Over where

import Prelude

import Control.Select (class Select)
import Control.Selective (class Selective)

data Over ∷ ∀ k. Type → k → Type
data Over m a = Over m

getOver ∷ ∀ m a. Over m a → m
getOver (Over m) = m

instance Functor (Over m) where
  map _ (Over a) = Over a

instance Semigroup m ⇒ Apply (Over m) where
  apply (Over a) (Over b) = Over (a <> b)

instance Monoid m ⇒ Applicative (Over m) where
  pure _ = Over mempty

instance Semigroup m ⇒ Select (Over m) where
  select (Over a) (Over b) = Over (a <> b)

instance Monoid m ⇒ Selective (Over m)
