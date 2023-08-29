module Control.MonadSelective where

import Prelude

import Control.Select (class Select, selectM)
import Control.Selective (class Selective)
import Data.Newtype (class Newtype)

newtype MonadSelective ∷ ∀ k. (k → Type) → k → Type
newtype MonadSelective m a = MonadSelective (m a)

derive instance Newtype (MonadSelective m a) _

derive newtype instance Functor m ⇒ Functor (MonadSelective m)
derive newtype instance Apply m ⇒ Apply (MonadSelective m)
derive newtype instance Applicative m ⇒ Applicative (MonadSelective m)
derive newtype instance Bind m ⇒ Bind (MonadSelective m)
derive newtype instance Monad m ⇒ Monad (MonadSelective m)

instance Monad m ⇒ Select (MonadSelective m) where
  select (MonadSelective e) (MonadSelective f) = MonadSelective (e `selectM` f)

instance Monad m ⇒ Selective (MonadSelective m)
