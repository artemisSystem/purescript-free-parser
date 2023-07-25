module Leibniz (Leibniz(..), type (~), refl, symm, trans, coerce, coerce') where

import Prelude

newtype Leibniz ∷ ∀ k. k → k → Type
newtype Leibniz a b = Leibniz (∀ f. f a → f b)

instance Semigroupoid Leibniz where
  compose (Leibniz f) (Leibniz g) = Leibniz (f <<< g)

instance Category Leibniz where
  identity = Leibniz \a → a

infix 4 type Leibniz as ~

refl ∷ ∀ a. a ~ a
refl = identity

newtype Flip ∷ ∀ k. k → k → Type
newtype Flip a b = Flip (Leibniz b a)

unFlip ∷ ∀ a b. Flip a b → Leibniz b a
unFlip (Flip fba) = fba

symm ∷ ∀ a b. (a ~ b) → (b ~ a)
symm (Leibniz f) = unFlip (f (Flip refl))

trans ∷ ∀ a b c. (a ~ b) → (b ~ c) → (a ~ c)
trans = flip compose

newtype Identity a = Identity a

unIdentity ∷ ∀ a. Identity a → a
unIdentity (Identity a) = a

coerce ∷ ∀ a b. (a ~ b) → a → b
coerce (Leibniz f) a = unIdentity (f (Identity a))

coerce' ∷ ∀ a b. (a ~ b) → b → a
coerce' = coerce <<< symm