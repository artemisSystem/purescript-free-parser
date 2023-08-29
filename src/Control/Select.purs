module Control.Select where

import Prelude

import Control.Apply (lift2)
import Control.Lazy (class Lazy, defer)
import Control.Monad.ST (ST)
import Data.Either (Either(..), note)
import Data.Identity (Identity)
import Data.Maybe (Maybe)
import Effect (Effect)
import Effect.Aff (Aff)

class Apply f ⇐ Select f where
  select ∷ ∀ a b. f (Either a b) → f (a → b) → f b

instance Select Array where
  select = selectM

instance Select Maybe where
  select = selectM

instance Select (Either e) where
  select = selectM

instance Select Effect where
  select = selectM

instance Select Aff where
  select = selectM

instance Select Identity where
  select = selectM

instance Select (ST h) where
  select = selectM

infixl 4 select as <*?

selectM ∷ ∀ m a b. Monad m ⇒ m (Either a b) → m (a → b) → m b
selectM e f = e >>= case _ of
  Left a → (_ $ a) <$> f
  Right b → pure b

selectA ∷ ∀ f a b. Apply f ⇒ f (Either a b) → f (a → b) → f b
selectA = lift2 case _ of
  Left a → \f → f a
  Right b → \_ → b

applyS ∷ ∀ f a b. Select f ⇒ f (a → b) → f a → f b
applyS f x = select (Left <$> f) ((#) <$> x)

whenS ∷ ∀ f. Select f ⇒ f Boolean → f Unit → f Unit
whenS cond f = select
  (cond <#> if _ then Left unit else Right unit)
  (f $> identity)

unlessS ∷ ∀ f. Select f ⇒ f Boolean → f Unit → f Unit
unlessS cond = whenS (not <$> cond)

branch ∷ ∀ f a b c. Select f ⇒ f (Either a b) → f (a → c) → f (b → c) → f c
branch cond l r = (map Left <$> cond) <*? (map Right <$> l) <*? r

ifS ∷ ∀ f a. Select f ⇒ f Boolean → f a → f a → f a
ifS cond a b = branch
  (cond <#> if _ then Left unit else Right unit)
  (const <$> a)
  (const <$> b)

fromMaybeS ∷ ∀ f a. Select f ⇒ f a → f (Maybe a) → f a
fromMaybeS default f = (note unit <$> f) <*? (const <$> default)

whileS ∷ ∀ f. Lazy (f Unit) ⇒ Select f ⇒ f Boolean → f Unit
whileS f = whenS f (defer \_ → whileS f)
