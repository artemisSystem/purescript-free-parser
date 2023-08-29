module Control.Selective.Free where

import Prelude

import Control.Applicative.Free.Trans (runExists')
import Control.MonadSelective (MonadSelective(..))
import Control.Select (class Select, (<*?))
import Control.Selective (class Selective)
import Data.Either (Either)
import Data.Exists (Exists, mkExists)
import Data.Newtype (un)

data ApplyF f b a = ApplyF (FreeS f (a → b)) (FreeS f a)

data SelectF f b a = SelectF (FreeS f (Either a b)) (FreeS f (a → b))

data FreeS f a
  = Pure a
  | Lift (f a)
  | Apply (Exists (ApplyF f a))
  | Select (Exists (SelectF f a))

instance Functor (FreeS f) where
  map = liftA1

instance Apply (FreeS f) where
  apply f a = Apply $ mkExists (ApplyF f a)

instance Applicative (FreeS f) where
  pure = Pure

instance Select (FreeS f) where
  select e f = Select $ mkExists (SelectF e f)

instance Selective (FreeS f)

liftF ∷ ∀ f. f ~> FreeS f
liftF = Lift

runFree ∷ ∀ f g. Selective g ⇒ (f ~> g) → (FreeS f ~> g)
runFree _ (Pure a) = pure a
runFree nat (Lift f) = nat f
runFree nat (Apply ex) = runExists' ex
  \(ApplyF f a) → runFree nat f <*> runFree nat a
runFree nat (Select ex) = runExists' ex
  \(SelectF e f) → runFree nat e <*? runFree nat f

runFreeM ∷ ∀ f g. Monad g ⇒ (f ~> g) → (FreeS f ~> g)
runFreeM nat = un MonadSelective <<< runFree (MonadSelective <<< nat)
