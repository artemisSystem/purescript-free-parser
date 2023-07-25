module FreeA where

import Prelude

import Control.Alt (class Alt, alt)
import Control.Alternative (class Alternative)
import Control.Apply (lift2)
import Control.Plus (class Plus, empty)
import Data.Exists (Exists, mkExists, runExists)
import Data.Monoid.Additive (Additive(..))
import Data.Newtype (un)
import Data.Tuple (Tuple(..), uncurry)

runExists' ∷ ∀ f r. Exists f → (∀ a. f a → r) → r
runExists' x f = runExists f x

data ApplyF f g a b = ApplyF (f (b → a)) (FreeAT f g b)

data FreeAF f g a = Pure a | Apply (Exists (ApplyF f g a))

instance Functor f ⇒ Functor (FreeAF f g) where
  map f (Pure a) = Pure (f a)
  map f (Apply ex) = Apply $ runExists' ex
    \(ApplyF g x) → mkExists $ ApplyF (map (_ >>> f) g) x

instance (Functor f, Applicative g) ⇒ Apply (FreeAF f g) where
  apply (Pure f) x = f <$> x
  apply (Apply ex) y = Apply $ runExists' ex
    \(ApplyF f x) → mkExists $ ApplyF (uncurry <$> f)
      (Tuple <$> x <*> FreeAT (pure y))

instance (Functor f, Applicative g) ⇒ Applicative (FreeAF f g) where
  pure = Pure

instance (Functor f, Applicative g, Semigroup a) ⇒ Semigroup (FreeAF f g a) where
  append = lift2 append

instance (Functor f, Applicative g, Monoid a) ⇒ Monoid (FreeAF f g a) where
  mempty = pure mempty

newtype FreeAT f g a = FreeAT (g (FreeAF f g a))

instance (Functor f, Functor g) ⇒ Functor (FreeAT f g) where
  map f (FreeAT free) = FreeAT $ map (map f) free

instance (Functor f, Applicative g) ⇒ Apply (FreeAT f g) where
  apply (FreeAT f) (FreeAT x) = FreeAT (apply <$> f <*> x)

instance (Functor f, Applicative g) ⇒ Applicative (FreeAT f g) where
  pure x = FreeAT (pure (pure x))

instance (Functor f, Alt g) ⇒ Alt (FreeAT f g) where
  alt (FreeAT f) (FreeAT g) = FreeAT (alt f g)

instance (Functor f, Plus g) ⇒ Plus (FreeAT f g) where
  empty = FreeAT empty

instance (Functor f, Alternative g) ⇒ Alternative (FreeAT f g)

liftF ∷ ∀ f g. Functor f ⇒ f ~> FreeAT f g
liftF f = Apply $ mkExists (ApplyF (const <$> f) (Pure unit))

{-}
peel ∷ ∀ f a r. (a → r) → (∀ b. ApplyF f a b → r) → FreeA f a → r
peel unPure _ (Pure a) = unPure a
peel _ unApply (Apply ex) = runExists' ex unApply

interpret ∷ ∀ f g. Applicative g ⇒ (f ~> g) → (FreeA f ~> g)
interpret nat = peel pure \(ApplyF f x) → nat f <*> interpret nat x

foldFree ∷ ∀ f a m. Monoid m ⇒ (∀ x. f x → m) → FreeA f a → m
foldFree _ (Pure _) = mempty
foldFree f (Apply ex) = runExists' ex
  \(ApplyF x cont) → f x <> foldFree f cont

count ∷ ∀ f a. FreeA f a → Int
count = un Additive <<< foldFree (\_ → Additive 1)

runFree ∷ ∀ f a. (∀ b. ApplyF f a b → FreeA f a) → FreeA f a → a
runFree run = peel identity (run >>> runFree run)

runFreeM
  ∷ ∀ f m a
  . Monad m
  ⇒ (∀ b. ApplyF f a b → m (FreeA f a))
  → FreeA f a
  → m a
runFreeM run = peel pure (run >=> runFreeM run)
