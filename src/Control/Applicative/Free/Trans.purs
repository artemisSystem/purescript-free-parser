module Control.Applicative.Free.Trans where

import Prelude

import Control.Alt (class Alt, (<|>))
import Control.Alternative (class Alternative)
import Control.Plus (class Plus, empty)
import Data.Const (Const(..))
import Data.Either (Either(..))
import Data.Exists (Exists, mkExists, runExists)
import Data.Functor.Coproduct (Coproduct(..))
import Data.Newtype (un)

runExists' ∷ ∀ f r. Exists f → (∀ a. f a → r) → r
runExists' x f = runExists f x

newtype ViaPlus ∷ ∀ k. (k → Type) → k → Type
newtype ViaPlus f a = ViaPlus (f a)

derive newtype instance Functor f ⇒ Functor (ViaPlus f)
instance (Plus f, Applicative f) ⇒ LiftAlt (ViaPlus f) where
  liftAlt a b = ViaPlus (pure a <|> pure b)
  empty' = ViaPlus empty

class LiftAlt f where
  liftAlt ∷ ∀ a. a → a → f a
  empty' ∷ ∀ a. f a

instance (Plus f, Applicative f) ⇒ LiftAlt (Coproduct f g) where
  liftAlt a b = Coproduct (Left (pure a <|> pure b))
  empty' = Coproduct (Left empty)

data HeadF f g a = Cis (f a) | Trans (g (FreeAT f g a))

data ApplyF f g b a = ApplyF (HeadF f g a) (FreeAT f g (a → b))

data FreeAT f g a = Pure a | Apply (Exists (ApplyF f g a))

instance Functor (FreeAT f g) where
  map f (Pure a) = Pure (f a)
  map f (Apply ex) = Apply $ runExists' ex \(ApplyF x g) →
    mkExists do ApplyF x (map (_ >>> f) g)

instance Apply (FreeAT f g) where
  apply (Pure f) x = f <$> x
  apply f (Pure x) = (_ $ x) <$> f
  apply (Apply ex) y = Apply $ runExists' ex \(ApplyF x f) →
    mkExists do ApplyF x (flip <$> f <*> y)

instance Applicative (FreeAT f g) where
  pure = Pure

instance LiftAlt g ⇒ Alt (FreeAT f g) where
  alt a b = wrap (liftAlt a b)

instance LiftAlt g ⇒ Plus (FreeAT f g) where
  empty = wrap empty'

instance LiftAlt g ⇒ Alternative (FreeAT f g)

liftF ∷ ∀ f g. f ~> FreeAT f g
liftF f = Apply $ mkExists $ ApplyF (Cis f) (Pure identity)

wrap ∷ ∀ f g a. g (FreeAT f g a) → FreeAT f g a
wrap g = Apply $ mkExists $ ApplyF (Trans g) (Pure identity)

liftOuter ∷ ∀ f g. Functor g ⇒ g ~> FreeAT f g
liftOuter g = wrap (Pure <$> g)

matchFree
  ∷ ∀ f g r
  . Functor g
  ⇒ (∀ x y. f x → r (x → y) → r y)
  → (∀ x y. g (r x) → r (x → y) → r y)
  → (∀ x. x → r x)
  → (FreeAT f g ~> r)
matchFree applyCis applyTrans pure' =
  case _ of
    Pure a → pure' a
    Apply ex → runExists' ex \(ApplyF head tail) → case head of
      (Cis f) → applyCis f (matchTail tail)
      (Trans g) → applyTrans (matchTail <$> g) (matchTail tail)
  where
  matchTail ∷ (FreeAT f g ~> r)
  matchTail f = matchFree applyCis applyTrans pure' f

runFree
  ∷ ∀ f g h
  . Functor g
  ⇒ Applicative h
  ⇒ (f ~> h)
  → (∀ x. g (h x) → h x)
  → (FreeAT f g ~> h)
runFree natF natG = matchFree
  (\head tail → (#) <$> natF head <*> tail)
  (\head tail → (#) <$> natG head <*> tail)
  pure

foldFree
  ∷ ∀ f g m a
  . Functor g
  ⇒ Monoid m
  ⇒ (∀ x. f x → m)
  → (g m → m)
  → (FreeAT f g a → m)
foldFree fromF fromG = un Const <<<
  runFree (Const <<< fromF) (Const <<< fromG <<< map (un Const))
