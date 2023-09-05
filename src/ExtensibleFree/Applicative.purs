module ExtensibleFree.Applicative (module Exports, runFree, foldFree) where

import Prelude

import Data.Const (Const(..))
import Data.Newtype (un)
import ExtensibleFree (APPLY, FreeV, LIFT, MAP, PURE, case_, handleApply, handleLift, handleMap, handlePure)
import ExtensibleFree (liftF) as Exports
import Type.Row (type (+))

type FreeA f = FreeV (LIFT f + MAP + APPLY + PURE + ())

runFree ∷ ∀ f g. Applicative g ⇒ (f ~> g) → (FreeA f ~> g)
runFree nat = go
  where
  go ∷ FreeA f ~> g
  go variant = case_
    # handleLift nat
    # handleMap go
    # handleApply go
    # handlePure
    # (_ $ variant)

foldFree ∷ ∀ f m a. Monoid m ⇒ (∀ b. f b → m) → FreeA f a → m
foldFree f = un Const <<< runFree (Const <<< f)
