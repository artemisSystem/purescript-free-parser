module Test.FreeS where

import Prelude

import Control.Select (ifS)
import Control.Selective (anyS)
import Control.Selective.Free (FreeS, liftF, runFree)
import Control.Selective.Over (Over(..), getOver)
import Control.Selective.Under (Under(..), getUnder)
import Data.Identity (Identity(..))
import Data.Monoid.Additive (Additive(..))
import Data.Newtype (un)
import Effect (Effect)
import Effect.Console (logShow)

action ∷ FreeS Identity Boolean
action = ado
  num ← ifS (lift true) (lift 4) (lift 6)
  num2 ← ifS (lift false) (lift 6) (lift 5)
  bool ← anyS lift [ false, false, true ]
  anyS lift [ true ]
  in num == num2 && bool
  where
  lift ∷ ∀ a. a → FreeS Identity a
  lift = liftF <<< Identity

countOver ∷ ∀ a. FreeS Identity a → Int
countOver = un Additive <<< getOver <<<
  runFree (\(Identity _) → Over (Additive 1))

countUnder ∷ ∀ a. FreeS Identity a → Int
countUnder = un Additive <<< getUnder <<<
  runFree (\(Identity _) → Under (Additive 1))

run ∷ ∀ a. FreeS Identity a → a
run = un Identity <<< runFree identity

main ∷ Effect Unit
main = do
  logShow (countOver action)
  logShow (countUnder action)
  logShow (run action)
