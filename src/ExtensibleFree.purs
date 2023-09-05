module ExtensibleFree where

import Prelude

import Control.Alt (class Alt, (<|>))
import Control.Alternative (class Alternative)
import Control.MonadPlus (class MonadPlus)
import Control.Plus (class Plus, empty)
import Control.Select (class Select, (<*?))
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

handleLiftAt
  ∷ ∀ @sym f g a r1 r1x r2
  . Row.Cons sym (LiftF f) r1x r1
  ⇒ Reflectable sym String
  ⇒ (f a → g a)
  → (FreeV' r1x r2 a → g a)
  → (FreeV' r1 r2 a → g a)
handleLiftAt nat = on @sym \(LiftF f) → nat f

handleLift
  ∷ ∀ f g a r1 r2
  . (f a → g a)
  → (FreeV' r1 r2 a → g a)
  → (FreeV' (LIFT f + r1) r2 a → g a)
handleLift = handleLiftAt @"lift"

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

handleMapAt
  ∷ ∀ @sym g a r1 r1x r2
  . Row.Cons sym MapF r1x r1
  ⇒ Reflectable sym String
  ⇒ Functor g
  ⇒ (FreeV r2 ~> g)
  → (FreeV' r1x r2 a → g a)
  → (FreeV' r1 r2 a → g a)
handleMapAt rec = on @sym \(MapF wrapper) → wrapper \f a → f <$> rec a

handleMap
  ∷ ∀ g a r1 r2
  . Functor g
  ⇒ (FreeV r2 ~> g)
  → (FreeV' r1 r2 a → g a)
  → (FreeV' (MAP + r1) r2 a → g a)
handleMap = handleMapAt @"map"

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

handleApplyAt
  ∷ ∀ @sym g a r1 r1x r2
  . Row.Cons sym ApplyF r1x r1
  ⇒ Reflectable sym String
  ⇒ Apply g
  ⇒ (FreeV r2 ~> g)
  → (FreeV' r1x r2 a → g a)
  → (FreeV' r1 r2 a → g a)
handleApplyAt rec = on @sym \(ApplyF wrapper) → wrapper \f a → rec f <*> rec a

handleApply
  ∷ ∀ g a r1 r2
  . Apply g
  ⇒ (FreeV r2 ~> g)
  → (FreeV' r1 r2 a → g a)
  → (FreeV' (APPLY + r1) r2 a → g a)
handleApply = handleApplyAt @"apply"

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

handleSelectAt
  ∷ ∀ @sym g a r1 r1x r2
  . Row.Cons sym SelectF r1x r1
  ⇒ Reflectable sym String
  ⇒ Select g
  ⇒ (FreeV r2 ~> g)
  → (FreeV' r1x r2 a → g a)
  → (FreeV' r1 r2 a → g a)
handleSelectAt rec = on @sym \(SelectF wrapper) → wrapper \e f → rec e <*? rec f

handleSelect
  ∷ ∀ g a r1 r2
  . Select g
  ⇒ (FreeV r2 ~> g)
  → (FreeV' r1 r2 a → g a)
  → (FreeV' (SELECT + r1) r2 a → g a)
handleSelect = handleSelectAt @"select"

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

handleBindAt
  ∷ ∀ @sym g a r1 r1x r2
  . Row.Cons sym BindF r1x r1
  ⇒ Reflectable sym String
  ⇒ Bind g
  ⇒ (FreeV r2 ~> g)
  → (FreeV' r1x r2 a → g a)
  → (FreeV' r1 r2 a → g a)
handleBindAt rec = on @sym
  \(BindF wrapper) → wrapper \a f → rec a >>= (f >>> rec)

handleBind
  ∷ ∀ g a r1 r2
  . Bind g
  ⇒ (FreeV r2 ~> g)
  → (FreeV' r1 r2 a → g a)
  → (FreeV' (BIND + r1) r2 a → g a)
handleBind = handleBindAt @"bind"

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

handlePureAt
  ∷ ∀ @sym g a r1 r1x r2
  . Row.Cons sym PureF r1x r1
  ⇒ Reflectable sym String
  ⇒ Applicative g
  ⇒ (FreeV' r1x r2 a → g a)
  → (FreeV' r1 r2 a → g a)
handlePureAt = on @sym \(PureF a) → pure a

handlePure
  ∷ ∀ g a r1 r2
  . Applicative g
  ⇒ (FreeV' r1 r2 a → g a)
  → (FreeV' (PURE + r1) r2 a → g a)
handlePure = handlePureAt @"pure"

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

instance (TypeEquals r (MAP + ALT + rx)) ⇒ Alt (FreeV r) where
  alt a b = fromNatF $ toNatF a `altF` toNatF b

handleAltAt
  ∷ ∀ @sym g a r1 r1x r2
  . Row.Cons sym AltF r1x r1
  ⇒ Reflectable sym String
  ⇒ Alt g
  ⇒ (FreeV r2 ~> g)
  → (FreeV' r1x r2 a → g a)
  → (FreeV' r1 r2 a → g a)
handleAltAt rec = on @sym \(AltF a b) → rec a <|> rec b

handleAlt
  ∷ ∀ g a r1 r2
  . Alt g
  ⇒ (FreeV r2 ~> g)
  → (FreeV' r1 r2 a → g a)
  → (FreeV' (ALT + r1) r2 a → g a)
handleAlt = handleAltAt @"alt"

data EmptyF ∷ (Type → Type) → Type → Type
data EmptyF rec a = EmptyF

type EMPTY r = (empty ∷ EmptyF | r)

emptyAt
  ∷ ∀ @sym rx r a. Reflectable sym String ⇒ Row.Cons sym EmptyF rx r ⇒ FreeV r a
emptyAt = inj @sym $ EmptyF

emptyF ∷ ∀ r a. FreeV (EMPTY + r) a
emptyF = emptyAt @"empty"

instance (TypeEquals r (MAP + ALT + EMPTY + rx)) ⇒ Plus (FreeV r) where
  empty = fromNatF emptyF

instance
  ( TypeEquals r (MAP + APPLY + PURE + ALT + EMPTY + rx)
  ) ⇒
  Alternative (FreeV r)

instance
  ( TypeEquals r (MAP + APPLY + SELECT + BIND + PURE + ALT + EMPTY + rx)
  ) ⇒
  MonadPlus (FreeV r)

handleEmptyAt
  ∷ ∀ @sym g a r1 r1x r2
  . Row.Cons sym EmptyF r1x r1
  ⇒ Reflectable sym String
  ⇒ Plus g
  ⇒ (FreeV' r1x r2 ~> g)
  → (FreeV' r1 r2 a → g a)
handleEmptyAt = on @sym \EmptyF → empty

handleEmpty
  ∷ ∀ g a r1 r2
  . Plus g
  ⇒ (FreeV' r1 r2 ~> g)
  → (FreeV' (EMPTY + r1) r2 a → g a)
handleEmpty = handleEmptyAt @"empty"
