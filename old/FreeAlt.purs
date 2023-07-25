module FreeAlt where

import Prelude

import Control.Alt (class Alt)
import Control.Alternative (class Alternative)
import Control.Apply (lift2)
import Control.Plus (class Plus)
import Data.Foldable (oneOfMap)
import Data.Functor.Compose (Compose(..))
import FreeA (FreeA)
import FreeA as FreeA

newtype FreeAlt f a = FreeAlt (Compose Array (FreeA f) a)

derive newtype instance Functor f ⇒ Functor (FreeAlt f)
derive newtype instance Functor f ⇒ Apply (FreeAlt f)
derive newtype instance Functor f ⇒ Applicative (FreeAlt f)
derive newtype instance Functor f ⇒ Alt (FreeAlt f)
derive newtype instance Functor f ⇒ Plus (FreeAlt f)
derive newtype instance Functor f ⇒ Alternative (FreeAlt f)

instance (Functor f, Semigroup a) ⇒ Semigroup (FreeAlt f a) where
  append = lift2 append

instance (Functor f, Monoid a) ⇒ Monoid (FreeAlt f a) where
  mempty = pure mempty

liftF ∷ ∀ f. Functor f ⇒ f ~> FreeAlt f
liftF = FreeA.liftF >>> pure >>> Compose >>> FreeAlt

interpret ∷ ∀ f g. Alternative g ⇒ (f ~> g) → (FreeAlt f ~> g)
interpret nat (FreeAlt (Compose xs)) = oneOfMap (FreeA.interpret nat) xs
