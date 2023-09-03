module VariantRec where

import Prelude

import Data.Maybe (Maybe(..))
import Data.Reflectable (class Reflectable, reflectType)
import Partial.Unsafe (unsafeCrashWith)
import Prim.Row as Row
import Type.Proxy (Proxy(..))
import Unsafe.Coerce (unsafeCoerce)

-- | First parameter is possible outer options
-- | Second parameter is possible inner options
foreign import data VariantRec'
  ∷ Row ((Type → Type) → Type → Type)
  → Row ((Type → Type) → Type → Type)
  → Type
  → Type

type VariantRec row = VariantRec' row row

type VariantRecRep ∷ ∀ k1 k2. (k1 → k2 → Type) → k1 → k2 → Type
type VariantRecRep f rec a =
  { type ∷ String
  , value ∷ f rec a
  }

inj
  ∷ ∀ @sym f rx r a
  . Reflectable sym String
  ⇒ Row.Cons sym f rx r
  ⇒ f (VariantRec r) a
  → VariantRec r a
inj value = coerceV { type: reflectType @sym Proxy, value }
  where
  coerceV ∷ VariantRecRep f (VariantRec r) a → VariantRec r a
  coerceV = unsafeCoerce

prj
  ∷ ∀ @sym f rx r a
  . Reflectable sym String
  ⇒ Row.Cons sym f rx r
  ⇒ VariantRec r a
  → Maybe (f (VariantRec r) a)
prj = on @sym Just \_ → Nothing

on
  ∷ ∀ @sym f a b rx r
  . Row.Cons sym f rx r
  ⇒ Reflectable sym String
  ⇒ (f (VariantRec r) a → b)
  → (VariantRec rx a → b)
  → VariantRec r a
  → b
on matching other variant = case coerceV variant of
  { type: t, value } →
    if t == reflectType @sym Proxy then matching value
    else other (reduce variant)
  where
  coerceV ∷ VariantRec r a → VariantRecRep f (VariantRec r) a
  coerceV = unsafeCoerce

  reduce ∷ VariantRec r a → VariantRec rx a
  reduce = unsafeCoerce

case_ ∷ ∀ a b. VariantRec () a → b
case_ variant = unsafeCrashWith $
  "VariantRec: pattern match failure on " <> (coerceV variant).type
  where
  coerceV ∷ ∀ f. VariantRec () a → VariantRecRep f (VariantRec ()) a
  coerceV = unsafeCoerce

default ∷ ∀ r a b. a → VariantRec r b → a
default a _ = a

expand ∷ ∀ lt mix gt a. Row.Union lt mix gt ⇒ VariantRec lt a → VariantRec gt a
expand = unsafeCoerce
