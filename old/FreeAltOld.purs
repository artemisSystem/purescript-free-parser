module FreeAltOld where

import Prelude

import Control.Alt (class Alt)
import Control.Alternative (class Alternative)
import Control.Plus (class Plus)
import Data.Exists (Exists, mkExists, runExists)
import Data.Functor.Compose (Compose)
import Data.Newtype (class Newtype, un)

data ApplyF f b a = ApplyF (f a) (FreeAlt f (a → b))

data AltF f a = Pure a | Apply (Exists (ApplyF f a))

instance Functor (AltF f) where
  map f (Pure a) = Pure (f a)
  map f (Apply ex) = Apply $
    runExists (\(ApplyF x g) → mkExists (ApplyF x (map (_ >>> f) g))) ex

instance Apply (AltF f) where
  apply (Pure f) x = map f x
  apply f (Pure x) = map (_ $ x) f
  apply (Apply ex) y = Apply $ runExists
    (\(ApplyF x f) → mkExists (ApplyF x (flip <$> f <*> (FreeAlt [ y ]))))
    ex

instance Applicative (AltF f) where
  pure = Pure

newtype FreeAlt f a = FreeAlt (Array (AltF f a))

derive instance Newtype (FreeAlt f a) _

instance Functor (FreeAlt f) where
  map f (FreeAlt xs) = FreeAlt $ map (map f) xs

instance Apply (FreeAlt f) where
  apply (FreeAlt xs) ys = FreeAlt (xs >>= \x → apply' x ys)
    where
    apply' ∷ ∀ a b. AltF f (a → b) → FreeAlt f a → Array (AltF f b)
    apply' (Pure f) x = un FreeAlt (map f x)
    apply' (Apply ex) y = runExists
      (\(ApplyF x f) → [ Apply $ mkExists (ApplyF x (flip <$> f <*> y)) ])
      ex

instance Applicative (FreeAlt f) where
  pure x = FreeAlt [ pure x ]

instance Alt (FreeAlt f) where
  alt (FreeAlt xs) (FreeAlt ys) = FreeAlt (xs <> ys)

instance Plus (FreeAlt f) where
  empty = FreeAlt []

instance Alternative (FreeAlt f)

data ApplyF' f b a = ApplyF' (f a) (FreeA f (a → b))

data FreeA f a = Pure' a | Apply' (Exists (ApplyF' f a))

instance Functor (FreeA f) where
  map f (Pure' a) = Pure' (f a)
  map f (Apply' ex) = Apply' $
    runExists (\(ApplyF' x g) → mkExists (ApplyF' x (map (_ >>> f) g))) ex

instance Apply (FreeA f) where
  apply (Pure' f) x = map f x
  apply f (Pure' x) = map (_ $ x) f
  apply (Apply' ex) y = Apply' $ runExists
    (\(ApplyF' x f) → mkExists (ApplyF' x (flip <$> f <*> y)))
    ex

instance Applicative (FreeA f) where
  pure = Pure'

newtype FreeAlt' f a = FreeAlt' (Compose Array (FreeA f) a)

derive newtype instance Functor (FreeAlt' f)
derive newtype instance Apply (FreeAlt' f)
derive newtype instance Applicative (FreeAlt' f)
derive newtype instance Alt (FreeAlt' f)
derive newtype instance Plus (FreeAlt' f)
derive newtype instance Alternative (FreeAlt' f)
