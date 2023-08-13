module Control.Selective.Under where

import Prelude

import Control.Select (class Select)
import Control.Selective (class Selective)

data Under ∷ ∀ k. Type → k → Type
data Under m a = Under m

getUnder ∷ ∀ m a. Under m a → m
getUnder (Under m) = m

instance Functor (Under m) where
  map _ (Under a) = Under a

instance Semigroup m ⇒ Apply (Under m) where
  apply (Under a) (Under b) = Under (a <> b)

instance Monoid m ⇒ Applicative (Under m) where
  pure _ = Under mempty

instance Semigroup m ⇒ Select (Under m) where
  select (Under a) _ = Under a

instance Monoid m ⇒ Selective (Under m)
