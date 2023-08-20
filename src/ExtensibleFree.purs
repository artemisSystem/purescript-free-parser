module ExtensibleFree where

import Prelude

import Control.Alt (class Alt)
import Control.Alternative (class Alternative)
import Control.MonadPlus (class MonadPlus)
import Control.Plus (class Plus)
import Control.Select (class Select)
import Control.Selective (class Selective)
import Data.Either (Either)
import Data.Newtype (class Newtype, un)
import Data.Reflectable (class Reflectable)
import Prim.Row as Row
import Type.Equality (class TypeEquals, proof)
import Type.Row (type (+))
import VariantRec (VariantRec, inj)

newtype ToNatF ∷ ∀ k1 k2. (k1 → k2 → Type) → k1 → k1 → Type
newtype ToNatF f a b = ToNatF (f a ~> f b)

toNatF ∷ ∀ @f @a @b. TypeEquals a b ⇒ f a ~> f b
toNatF = case proof (ToNatF \x → x) of ToNatF f → f

newtype FromNatF ∷ ∀ k1 k2. (k1 → k2 → Type) → k1 → k1 → Type
newtype FromNatF f a b = FromNatF (f b ~> f a)

fromNatF ∷ ∀ @f @a @b. TypeEquals a b ⇒ f b ~> f a
fromNatF = case proof (FromNatF \x → x) of FromNatF f → f

newtype Free r a = Free (VariantRec r a)

derive instance Newtype (Free r a) _

newtype LiftF ∷ (Type → Type) → (Type → Type) → Type → Type
newtype LiftF f rec a = LiftF (f a)

type LIFT f r = (lift ∷ LiftF f | r)

liftAt
  ∷ ∀ @sym rx r f a
  . Reflectable sym String
  ⇒ Row.Cons sym (LiftF f) rx r
  ⇒ f a
  → Free r a
liftAt = Free <<< inj @sym <<< LiftF

liftF ∷ ∀ r f a. f a → Free (LIFT f + r) a
liftF = liftAt @"lift"

newtype MapF rec a = MapF (∀ r. (∀ x. (x → a) → rec x → r) → r)
type MAP r = (map ∷ MapF | r)

mapAt
  ∷ ∀ @sym rx r a b
  . Reflectable sym String
  ⇒ Row.Cons sym MapF rx r
  ⇒ (a → b)
  → Free r a
  → Free r b
mapAt f (Free a) = Free $ inj @sym $ MapF \r → r f a

mapF ∷ ∀ r a b. (a → b) → Free (MAP + r) a → Free (MAP + r) b
mapF = mapAt @"map"

instance (TypeEquals r (MAP + rx)) ⇒ Functor (Free r) where
  map f a = fromNatF $ f `mapF` toNatF a

newtype ApplyF rec a = ApplyF (∀ r. (∀ x. rec (x → a) → rec x → r) → r)
type APPLY r = (apply ∷ ApplyF | r)

applyAt
  ∷ ∀ @sym rx r a b
  . Reflectable sym String
  ⇒ Row.Cons sym ApplyF rx r
  ⇒ Free r (a → b)
  → Free r a
  → Free r b
applyAt (Free f) (Free a) = Free $ inj @sym $ ApplyF \r → r f a

applyF
  ∷ ∀ r a b
  . Free (APPLY + r) (a → b)
  → Free (APPLY + r) a
  → Free (APPLY + r) b
applyF = applyAt @"apply"

instance (TypeEquals r (MAP + APPLY + rx)) ⇒ Apply (Free r) where
  apply f a = fromNatF $ toNatF f `applyF` toNatF a

newtype SelectF rec a = SelectF
  (∀ r. (∀ x. rec (Either x a) → rec (x → a) → r) → r)

type SELECT r = (select ∷ SelectF | r)

selectAt
  ∷ ∀ @sym rx r a b
  . Reflectable sym String
  ⇒ Row.Cons sym SelectF rx r
  ⇒ Free r (Either a b)
  → Free r (a → b)
  → Free r b
selectAt (Free e) (Free f) = Free $ inj @sym $ SelectF \r → r e f

selectF
  ∷ ∀ r a b
  . Free (SELECT + r) (Either a b)
  → Free (SELECT + r) (a → b)
  → Free (SELECT + r) b
selectF = selectAt @"select"

instance (TypeEquals r (MAP + APPLY + SELECT + rx)) ⇒ Select (Free r) where
  select e f = fromNatF $ toNatF e `selectF` toNatF f

newtype BindF rec a = BindF (∀ r. (∀ x. rec x → (x → rec a) → r) → r)
type BIND r = (bind ∷ BindF | r)

bindAt
  ∷ ∀ @sym rx r a b
  . Reflectable sym String
  ⇒ Row.Cons sym BindF rx r
  ⇒ Free r a
  → (a → Free r b)
  → Free r b
bindAt (Free a) f = Free $ inj @sym $ BindF \r → r a (f >>> un Free)

bindF ∷ ∀ r a b. Free (BIND + r) a → (a → Free (BIND + r) b) → Free (BIND + r) b
bindF = bindAt @"bind"

instance (TypeEquals r (MAP + APPLY + SELECT + BIND + rx)) ⇒ Bind (Free r) where
  bind a f = fromNatF $ toNatF a `bindF` (f >>> toNatF)

newtype PureF ∷ (Type → Type) → Type → Type
newtype PureF rec a = PureF a

type PURE r = (pure ∷ PureF | r)

pureAt
  ∷ ∀ @sym rx r a
  . Reflectable sym String
  ⇒ Row.Cons sym PureF rx r
  ⇒ a
  → Free r a
pureAt a = Free $ inj @sym $ PureF a

pureF ∷ ∀ r a. a → Free (PURE + r) a
pureF = pureAt @"pure"

instance (TypeEquals r (MAP + APPLY + PURE + rx)) ⇒ Applicative (Free r) where
  pure a = fromNatF $ pureF a

instance (TypeEquals r (MAP + APPLY + SELECT + PURE + rx)) ⇒ Selective (Free r)

instance
  ( TypeEquals r (MAP + APPLY + SELECT + BIND + PURE + rx)
  ) ⇒
  Monad (Free r)

data AltF ∷ (Type → Type) → Type → Type
data AltF rec a = AltF (rec a) (rec a)

type ALT r = (alt ∷ AltF | r)

altAt
  ∷ ∀ @sym rx r a
  . Reflectable sym String
  ⇒ Row.Cons sym AltF rx r
  ⇒ Free r a
  → Free r a
  → Free r a
altAt (Free a) (Free b) = Free $ inj @sym $ AltF a b

altF ∷ ∀ r a. Free (ALT + r) a → Free (ALT + r) a → Free (ALT + r) a
altF = altAt @"alt"

instance (TypeEquals r (MAP + APPLY + ALT + rx)) ⇒ Alt (Free r) where
  alt a b = fromNatF $ toNatF a `altF` toNatF b

data EmptyF ∷ (Type → Type) → Type → Type
data EmptyF rec a = EmptyF

type EMPTY r = (empty ∷ EmptyF | r)

emptyAt
  ∷ ∀ @sym rx r a. Reflectable sym String ⇒ Row.Cons sym EmptyF rx r ⇒ Free r a
emptyAt = Free $ inj @sym $ EmptyF

emptyF ∷ ∀ r a. Free (EMPTY + r) a
emptyF = emptyAt @"empty"

instance (TypeEquals r (MAP + APPLY + ALT + EMPTY + rx)) ⇒ Plus (Free r) where
  empty = fromNatF emptyF

instance
  ( TypeEquals r (MAP + APPLY + PURE + ALT + EMPTY + rx)
  ) ⇒
  Alternative (Free r)

instance
  ( TypeEquals r (MAP + APPLY + SELECT + BIND + PURE + ALT + EMPTY + rx)
  ) ⇒
  MonadPlus (Free r)
