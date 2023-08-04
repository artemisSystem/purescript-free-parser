module Test.Main where

import Prelude

import Control.Alt ((<|>))
import Control.Alternative.Free (FreeAlt)
import Control.Alternative.Free as Alt
import Control.Applicative.Free (FreeA, foldFree, liftF, runFree)
import Control.Monad.State (State, runState)
import Control.Monad.State as State
import Data.Const (Const(..))
import Data.Foldable (intercalate, length, sum)
import Data.Functor.Compose (Compose(..))
import Data.Monoid.Additive (Additive(..))
import Data.Monoid.Multiplicative (Multiplicative(..))
import Data.Newtype (un)
import Data.String (CodePoint, codePointFromChar)
import Data.Tuple (Tuple)
import Data.Unfoldable1 (singleton)
import Effect (Effect)
import Effect.Console (log)
import FreeParser (Parser, label, literal, many, manySpace, string)
import FreeParser.BnfStmt (printBnf)
import Safe.Coerce (coerce)

data OpF a = Add Int a | Mul Int a | Get (Int → a)

derive instance Functor OpF

type Op = FreeA OpF

addOp ∷ Int → Op Unit
addOp x = liftF (Add x unit)

mulOp ∷ Int → Op Unit
mulOp x = liftF (Mul x unit)

getOp ∷ Op Int
getOp = liftF (Get identity)

runOp ∷ ∀ a. Int → Op a → Tuple a Int
runOp init = flip runState init <<< runFree case _ of
  Add x r → State.modify (_ + x) $> r
  Mul x r → State.modify (_ * x) $> r
  Get f → State.gets f

runOpAddFirst ∷ ∀ a. Int → Op a → Tuple a Int
runOpAddFirst init = map eval <<< flip runState mempty <<< accumulate
  where
  accumulate ∷ Op a → State { add ∷ Additive Int, mul ∷ Multiplicative Int } a
  accumulate = runFree case _ of
    Add x r → State.modify (_ <> { mul: mempty, add: Additive x }) $> r
    Mul x r → State.modify (_ <> { add: mempty, mul: Multiplicative x }) $> r
    Get f → State.gets (eval >>> f)
  eval { add: (Additive a), mul: (Multiplicative m) } = m * (a + init)

structure ∷ ∀ a. Op a → Array String
structure = un Const <<< runFree case _ of
  Add _ _ → Const [ "Add" ]
  Mul _ _ → Const [ "Mul" ]
  Get _ → Const [ "Get" ]

count ∷ ∀ a. Op a → Int
count = un Additive <<< foldFree \_ → Additive 1

type OpCount = { add ∷ Int, mul ∷ Int, get ∷ Int }
type OpCount' = { add ∷ Additive Int, mul ∷ Additive Int, get ∷ Additive Int }

countOps ∷ ∀ a. Op a → OpCount
countOps = coerce <<< foldFree case _ of
  Add _ _ → i { add = Additive 1 }
  Mul _ _ → i { mul = Additive 1 }
  Get _ → i { get = Additive 1 }
  where
  i ∷ OpCount'
  i = mempty

type OpAlt = FreeAlt OpF

addOpAlt ∷ Int → OpAlt Unit
addOpAlt x = Alt.liftF (Add x unit)

mulOpAlt ∷ Int → OpAlt Unit
mulOpAlt x = Alt.liftF (Mul x unit)

getOpAlt ∷ OpAlt Int
getOpAlt = Alt.liftF (Get identity)

runOpAlt ∷ ∀ a. Int → OpAlt a → Array (Tuple a Int)
runOpAlt init = map (flip runState init) <<< un Compose <<<
  Alt.runFree case _ of
    Add x r → Compose [ State.modify (_ + x) $> r ]
    Mul x r → Compose [ State.modify (_ * x) $> r ]
    Get f → Compose [ State.gets f ]

type Array' = FreeA Array

arrayStructure ∷ ∀ a. Array' a → Array Int
arrayStructure = un Const <<< runFree (Const <<< singleton <<< length)

action ∷ Op String
action = ado
  addOp 1
  mulOp 2
  addOp 3
  r ← getOp
  mulOp 3
  addOp 4
  in "Intermediate value: " <> show r

actionAlt ∷ OpAlt String
actionAlt = ado
  addOpAlt 1
  r1 ← getOpAlt
  mulOpAlt 2 <|> addOpAlt 2 <|> mulOpAlt 3
  r2 ← getOpAlt
  addOpAlt 4
  in "i1: " <> show r1 <> ", i2: " <> show r2

actionArray ∷ Array' Unit
actionArray = ado
  liftF [ 1, 2, 3 ]
  liftF $ [ "a", "b" ] <|> [ "c", "d" ]
  liftF [ true, true, true, false, false ]
  liftF [ unit, unit ]
  in unit

parser ∷ Parser CodePoint { a ∷ String, b ∷ Int }
parser = label "parser" ado
  manySpace
  str ← label "strings" $ string "abc" <|> string "123" <|> string "abcd"
  manySpace
  int ← label "ones" $ sum <$> many (literal (codePointFromChar '1') $> 1)
  in { a: str, b: int }

main ∷ Effect Unit
main = do
  don't \_ → do
    log "Op:"
    log ("start 0: " <> show do runOp 0 action)
    log ("start 1: " <> show do runOp 1 action)
    log ("addFirst, start 0: " <> show do runOpAddFirst 0 action)
    log ("addFirst, start 1: " <> show do runOpAddFirst 1 action)
    log ("count: " <> show do count action)
    log ("count ops: " <> show do countOps action)
    log ("structure: " <> intercalate ", " do structure action)
    log "Array':"
    log ("structure: " <> show do arrayStructure actionArray)
    log "OpAlt:"
    log ("start 0: " <> show do runOpAlt 0 actionAlt)
    log ("start 1: " <> show do runOpAlt 1 actionAlt)

  log (printBnf parser)
  where
  don't _ = pure unit
