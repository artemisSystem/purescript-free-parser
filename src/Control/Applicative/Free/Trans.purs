module Control.Applicative.Free.Trans where

import Prelude

import Control.Alt (class Alt, alt)
import Control.Alternative (class Alternative)
import Control.Plus (class Plus, empty)
import Data.Const (Const(..))
import Data.Exists (Exists, mkExists, runExists)
import Data.Newtype (un)

runExists' ∷ ∀ f r. Exists f → (∀ a. f a → r) → r
runExists' x f = runExists f x

data ApplyF f g b a = ApplyF (f a) (FreeAT f g (a → b))

data ApplicativeF f g a = Pure a | Apply (Exists (ApplyF f g a))

newtype FreeAT f g a = FreeAT (g (ApplicativeF f g a))

-- ApplicativeF instances
instance Functor g ⇒ Functor (ApplicativeF f g) where
  map f (Pure a) = Pure (f a)
  map f (Apply ex) = Apply $ runExists' ex \(ApplyF x g) →
    mkExists do ApplyF x (map (_ >>> f) g)

instance Applicative g ⇒ Apply (ApplicativeF f g) where
  apply (Pure f) x = f <$> x
  apply f (Pure x) = (_ $ x) <$> f
  apply (Apply ex) y = Apply $ runExists' ex \(ApplyF x f) →
    mkExists do ApplyF x (flip <$> f <*> FreeAT (pure y))

instance Applicative g ⇒ Applicative (ApplicativeF f g) where
  pure = Pure

-- FreeAT instances
instance Functor g ⇒ Functor (FreeAT f g) where
  map f (FreeAT g) = FreeAT (map f <$> g)

instance Applicative g ⇒ Apply (FreeAT f g) where
  apply (FreeAT f) (FreeAT x) = FreeAT (apply <$> f <*> x)

instance Applicative g ⇒ Applicative (FreeAT f g) where
  pure = FreeAT <<< pure <<< Pure

instance Alt g ⇒ Alt (FreeAT f g) where
  alt (FreeAT f) (FreeAT g) = FreeAT (alt f g)

instance Plus g ⇒ Plus (FreeAT f g) where
  empty = FreeAT empty

instance Alternative g ⇒ Alternative (FreeAT f g)

liftF ∷ ∀ f g. Applicative g ⇒ f ~> FreeAT f g
liftF f = FreeAT $ pure $ Apply $ mkExists $ ApplyF f (pure identity)

liftOuter ∷ ∀ f g. Functor g ⇒ g ~> FreeAT f g
liftOuter f = FreeAT (Pure <$> f)

matchFree
  ∷ ∀ f g r
  . Functor g
  ⇒ (∀ x y. f x → r (x → y) → r y)
  → (∀ x. x → r x)
  → (∀ x. g (r x) → r x)
  → (FreeAT f g ~> r)
matchFree apply' pure' natG (FreeAT ft) = natG $ ft <#> case _ of
  Pure a → pure' a
  Apply ex → runExists' ex \(ApplyF f fs) →
    apply' f (matchFree apply' pure' natG fs)

runFree
  ∷ ∀ f g h
  . Functor g
  ⇒ Applicative h
  ⇒ (f ~> h)
  → (∀ x. g (h x) → h x)
  → (FreeAT f g ~> h)
runFree natF = matchFree (\f g → (flip ($)) <$> natF f <*> g) pure

foldFree
  ∷ ∀ f g m a
  . Functor g
  ⇒ Monoid m
  ⇒ (∀ x. f x → m)
  → (g m → m)
  → (FreeAT f g a → m)
foldFree fromF fromG = un Const <<<
  runFree (Const <<< fromF) (Const <<< fromG <<< map (un Const))
