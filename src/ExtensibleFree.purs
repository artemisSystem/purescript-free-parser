module ExtensibleFree where

import Prelude

import Control.Alt (class Alt)
import Control.Alternative (class Alternative)
import Control.MonadPlus (class MonadPlus)
import Control.Plus (class Plus)
import Control.Select (class Select)
import Control.Selective (class Selective)
import Data.Either (Either)
import Data.Maybe (Maybe(..))
import Data.Reflectable (class Reflectable, reflectType)
import Partial.Unsafe (unsafeCrashWith)
import Prim.Row as Row
import Type.Equality (class TypeEquals, proof)
import Type.Proxy (Proxy(..))
import Type.Row (type (+))
import Unsafe.Coerce (unsafeCoerce)

-- | First parameter is possible outer options
-- | Second parameter is possible inner options
foreign import data FreeV'
  ∷ Row ((Type → Type) → Type → Type)
  → Row ((Type → Type) → Type → Type)
  → Type
  → Type

type FreeV row = FreeV' row row

type FreeVRep ∷ ∀ k1 k2. (k1 → k2 → Type) → k1 → k2 → Type
type FreeVRep f rec a =
  { type ∷ String
  , value ∷ f rec a
  }

inj
  ∷ ∀ @sym f rx r1 r2 a
  . Reflectable sym String
  ⇒ Row.Cons sym f rx r1
  ⇒ f (FreeV r2) a
  → FreeV' r1 r2 a
inj value = coerceV { type: reflectType @sym Proxy, value }
  where
  coerceV ∷ FreeVRep f (FreeV r2) a → FreeV' r1 r2 a
  coerceV = unsafeCoerce

prj
  ∷ ∀ @sym f rx r1 r2 a
  . Reflectable sym String
  ⇒ Row.Cons sym f rx r1
  ⇒ FreeV' r1 r2 a
  → Maybe (f (FreeV r2) a)
prj = on @sym Just \_ → Nothing

on
  ∷ ∀ @sym f a b rx row innerRow
  . Row.Cons sym f rx row
  ⇒ Reflectable sym String
  ⇒ (f (FreeV innerRow) a → b)
  → (FreeV' rx innerRow a → b)
  → FreeV' row innerRow a
  → b
on matching other variant = case coerceV variant of
  { type: t, value } →
    if t == reflectType @sym Proxy then matching value
    else other (reduce variant)
  where
  coerceV ∷ FreeV' row innerRow a → FreeVRep f (FreeV innerRow) a
  coerceV = unsafeCoerce

  reduce ∷ FreeV' row innerRow a → FreeV' rx innerRow a
  reduce = unsafeCoerce

case_ ∷ ∀ a b r. FreeV' () r a → b
case_ variant = unsafeCrashWith $
  "FreeV: pattern match failure on " <> (absurd variant).type
  where
  absurd ∷ ∀ f. FreeV' () r a → FreeVRep f (FreeV r) a
  absurd = unsafeCoerce

default ∷ ∀ r1 r2 a b. a → FreeV' r1 r2 b → a
default a _ = a

expand
  ∷ ∀ lt1 mix1 gt1 lt2 mix2 gt2 a
  . Row.Union lt1 mix1 gt1
  ⇒ Row.Union lt2 mix2 gt2
  ⇒ FreeV' lt1 lt2 a
  → FreeV' gt1 gt2 a
expand = unsafeCoerce

newtype ToNatF ∷ ∀ k1 k2. (k1 → k1 → k2 → Type) → k1 → k1 → Type
newtype ToNatF f a b = ToNatF (f a a ~> f b b)

toNatF ∷ ∀ @f @a @b. TypeEquals a b ⇒ f a a ~> f b b
toNatF = case proof (ToNatF \x → x) of ToNatF f → f

newtype FromNatF ∷ ∀ k1 k2. (k1 → k1 → k2 → Type) → k1 → k1 → Type
newtype FromNatF f a b = FromNatF (f b b ~> f a a)

fromNatF ∷ ∀ @f @a @b. TypeEquals a b ⇒ f b b ~> f a a
fromNatF = case proof (FromNatF \x → x) of FromNatF f → f

newtype LiftF ∷ (Type → Type) → (Type → Type) → Type → Type
newtype LiftF f rec a = LiftF (f a)

type LIFT f r = (lift ∷ LiftF f | r)

liftAt
  ∷ ∀ @sym rx r f a
  . Reflectable sym String
  ⇒ Row.Cons sym (LiftF f) rx r
  ⇒ f a
  → FreeV r a
liftAt = inj @sym <<< LiftF

liftF ∷ ∀ r f a. f a → FreeV (LIFT f + r) a
liftF = liftAt @"lift"

newtype MapF rec a = MapF (∀ r. (∀ x. (x → a) → rec x → r) → r)
type MAP r = (map ∷ MapF | r)

mapAt
  ∷ ∀ @sym rx r a b
  . Reflectable sym String
  ⇒ Row.Cons sym MapF rx r
  ⇒ (a → b)
  → FreeV r a
  → FreeV r b
mapAt f a = inj @sym $ MapF \r → r f a

mapF ∷ ∀ r a b. (a → b) → FreeV (MAP + r) a → FreeV (MAP + r) b
mapF = mapAt @"map"

instance (TypeEquals r (MAP + rx)) ⇒ Functor (FreeV r) where
  map f a = fromNatF $ f `mapF` toNatF a

newtype ApplyF rec a = ApplyF (∀ r. (∀ x. rec (x → a) → rec x → r) → r)
type APPLY r = (apply ∷ ApplyF | r)

applyAt
  ∷ ∀ @sym rx r a b
  . Reflectable sym String
  ⇒ Row.Cons sym ApplyF rx r
  ⇒ FreeV r (a → b)
  → FreeV r a
  → FreeV r b
applyAt f a = inj @sym $ ApplyF \r → r f a

applyF
  ∷ ∀ r a b
  . FreeV (APPLY + r) (a → b)
  → FreeV (APPLY + r) a
  → FreeV (APPLY + r) b
applyF = applyAt @"apply"

instance (TypeEquals r (MAP + APPLY + rx)) ⇒ Apply (FreeV r) where
  apply f a = fromNatF $ toNatF f `applyF` toNatF a

newtype SelectF rec a = SelectF
  (∀ r. (∀ x. rec (Either x a) → rec (x → a) → r) → r)

type SELECT r = (select ∷ SelectF | r)

selectAt
  ∷ ∀ @sym rx r a b
  . Reflectable sym String
  ⇒ Row.Cons sym SelectF rx r
  ⇒ FreeV r (Either a b)
  → FreeV r (a → b)
  → FreeV r b
selectAt e f = inj @sym $ SelectF \r → r e f

selectF
  ∷ ∀ r a b
  . FreeV (SELECT + r) (Either a b)
  → FreeV (SELECT + r) (a → b)
  → FreeV (SELECT + r) b
selectF = selectAt @"select"

instance (TypeEquals r (MAP + APPLY + SELECT + rx)) ⇒ Select (FreeV r) where
  select e f = fromNatF $ toNatF e `selectF` toNatF f

newtype BindF rec a = BindF (∀ r. (∀ x. rec x → (x → rec a) → r) → r)
type BIND r = (bind ∷ BindF | r)

bindAt
  ∷ ∀ @sym rx r a b
  . Reflectable sym String
  ⇒ Row.Cons sym BindF rx r
  ⇒ FreeV r a
  → (a → FreeV r b)
  → FreeV r b
bindAt a f = inj @sym $ BindF \r → r a f

bindF
  ∷ ∀ r a b. FreeV (BIND + r) a → (a → FreeV (BIND + r) b) → FreeV (BIND + r) b
bindF = bindAt @"bind"

instance (TypeEquals r (MAP + APPLY + SELECT + BIND + rx)) ⇒ Bind (FreeV r) where
  bind a f = fromNatF $ toNatF a `bindF` (f >>> toNatF)

newtype PureF ∷ (Type → Type) → Type → Type
newtype PureF rec a = PureF a

type PURE r = (pure ∷ PureF | r)

pureAt
  ∷ ∀ @sym rx r a
  . Reflectable sym String
  ⇒ Row.Cons sym PureF rx r
  ⇒ a
  → FreeV r a
pureAt a = inj @sym $ PureF a

pureF ∷ ∀ r a. a → FreeV (PURE + r) a
pureF = pureAt @"pure"

instance (TypeEquals r (MAP + APPLY + PURE + rx)) ⇒ Applicative (FreeV r) where
  pure a = fromNatF $ pureF a

instance (TypeEquals r (MAP + APPLY + SELECT + PURE + rx)) ⇒ Selective (FreeV r)

instance
  ( TypeEquals r (MAP + APPLY + SELECT + BIND + PURE + rx)
  ) ⇒
  Monad (FreeV r)

data AltF ∷ (Type → Type) → Type → Type
data AltF rec a = AltF (rec a) (rec a)

type ALT r = (alt ∷ AltF | r)

altAt
  ∷ ∀ @sym rx r a
  . Reflectable sym String
  ⇒ Row.Cons sym AltF rx r
  ⇒ FreeV r a
  → FreeV r a
  → FreeV r a
altAt a b = inj @sym $ AltF a b

altF ∷ ∀ r a. FreeV (ALT + r) a → FreeV (ALT + r) a → FreeV (ALT + r) a
altF = altAt @"alt"

instance (TypeEquals r (MAP + APPLY + ALT + rx)) ⇒ Alt (FreeV r) where
  alt a b = fromNatF $ toNatF a `altF` toNatF b

data EmptyF ∷ (Type → Type) → Type → Type
data EmptyF rec a = EmptyF

type EMPTY r = (empty ∷ EmptyF | r)

emptyAt
  ∷ ∀ @sym rx r a. Reflectable sym String ⇒ Row.Cons sym EmptyF rx r ⇒ FreeV r a
emptyAt = inj @sym $ EmptyF

emptyF ∷ ∀ r a. FreeV (EMPTY + r) a
emptyF = emptyAt @"empty"

instance (TypeEquals r (MAP + APPLY + ALT + EMPTY + rx)) ⇒ Plus (FreeV r) where
  empty = fromNatF emptyF

instance
  ( TypeEquals r (MAP + APPLY + PURE + ALT + EMPTY + rx)
  ) ⇒
  Alternative (FreeV r)

instance
  ( TypeEquals r (MAP + APPLY + SELECT + BIND + PURE + ALT + EMPTY + rx)
  ) ⇒
  MonadPlus (FreeV r)
