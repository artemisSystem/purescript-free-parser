module Control.Selective where

import Prelude

import Control.Monad.ST (ST)
import Control.Select (class Select, ifS)
import Data.Either (Either)
import Data.Foldable (class Foldable, foldr)
import Data.Identity (Identity)
import Data.Maybe (Maybe)
import Effect (Effect)
import Effect.Aff (Aff)

class (Applicative f, Select f) ⇐ Selective f

instance Selective Array
instance Selective Maybe
instance Selective (Either e)
instance Selective Effect
instance Selective Aff
instance Selective Identity
instance Selective (ST h)

orS ∷ ∀ f. Selective f ⇒ f Boolean → f Boolean → f Boolean
orS x y = ifS x (pure true) y

infixr 2 orS as <||>

andS ∷ ∀ f. Selective f ⇒ f Boolean → f Boolean → f Boolean
andS x y = ifS x y (pure false)

infixr 3 andS as <&&>

anyS ∷ ∀ f t a. Selective f ⇒ Foldable t ⇒ (a → f Boolean) → t a → f Boolean
anyS pred = foldr (pred >>> orS) (pure false)

allS ∷ ∀ f t a. Selective f ⇒ Foldable t ⇒ (a → f Boolean) → t a → f Boolean
allS pred = foldr (pred >>> andS) (pure true)
