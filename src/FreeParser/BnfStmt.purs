module FreeParser.BnfStmt where

import Prelude

import Control.Applicative.Free.Trans (foldFree, runExists', runFree')
import Control.Monad.State (State, execState)
import Control.Monad.State as State
import Data.Const (Const(..))
import Data.Foldable (intercalate)
import Data.FoldableWithIndex (foldMapWithIndex)
import Data.Functor.Compose (Compose(..))
import Data.Generic.Rep (class Generic)
import Data.Map (Map)
import Data.Map as Map
import Data.Show.Generic (genericShow)
import FreeParser (ManyF(..), OptionF(..), Parser, ParserBase(..), ParserControl(..), TaggedFunction(..))

data BnfStmt
  = ConcatBnf (Array BnfStmt)
  | AltBnf BnfStmt BnfStmt
  | BnfMany BnfStmt
  | BnfOption BnfStmt
  | BnfParens BnfStmt
  | BnfReference String
  | BnfLiteral String

derive instance Generic BnfStmt _

instance Show BnfStmt where
  show x = genericShow x

instance Semigroup BnfStmt where
  append (ConcatBnf a) (ConcatBnf b) = ConcatBnf (a <> b)
  append a (ConcatBnf []) = a
  append (ConcatBnf []) b = b
  append a b = ConcatBnf [ a, b ]

instance Monoid BnfStmt where
  mempty = ConcatBnf []

printBnfStmt ∷ BnfStmt → String
printBnfStmt (ConcatBnf stmts) = intercalate ", " (printBnfStmt <$> stmts)
printBnfStmt (AltBnf a b) =
  "(" <> printBnfStmt a <> " | " <> printBnfStmt b <> ")"
printBnfStmt (BnfMany stmt) = "{" <> printBnfStmt stmt <> "}"
printBnfStmt (BnfOption stmt) = "[" <> printBnfStmt stmt <> "]"
printBnfStmt (BnfParens stmt) = "(" <> printBnfStmt stmt <> ")"
printBnfStmt (BnfReference ref) = ref
printBnfStmt (BnfLiteral lit) = "\"" <> lit <> "\""

toBnfStmt ∷ ∀ char a. Parser char a → BnfStmt
toBnfStmt = foldFree base control
  where
  base ∷ ∀ x. ParserBase char x → BnfStmt
  base (Eof _) = BnfLiteral "EoF"
  base (Satisfies (TaggedFunction tag _) _) = BnfLiteral tag
  base (Many ex) = runExists' ex \(ManyF parser _) → BnfMany (toBnfStmt parser)
  base (Option ex) = runExists' ex \(OptionF parser _) →
    BnfOption (toBnfStmt parser)

  control ∷ ParserControl BnfStmt → BnfStmt
  control (Label str _) = BnfReference str
  control (Group stmt) = BnfParens stmt
  control (Alt a b) = AltBnf a b
  control Empty = mempty

type ConstState ∷ ∀ k. Type → k → Type
type ConstState char = Compose
  (State (Map String (Parser char Unit)))
  (Const Unit)

lift ∷ ∀ char x. State (Map String (Parser char Unit)) Unit → ConstState char x
lift s = Compose (s $> Const unit)

lower ∷ ∀ char x. ConstState char x → State (Map String (Parser char Unit)) Unit
lower (Compose s) = void s

findLabels ∷ ∀ char a. Parser char a → Map String (Parser char Unit)
findLabels p = execState (find p) Map.empty
  where
  find ∷ ∀ x. Parser char x → State (Map String (Parser char Unit)) Unit
  find parser = lower (runFree' base control parser)

  base ∷ ParserBase char ~> ConstState char
  base (Many ex) = runExists' ex \(ManyF parser _) → lift (find parser)
  base (Option ex) = runExists' ex \(OptionF parser _) → lift (find parser)
  base _ = lift (pure unit)

  control ∷ ∀ x. ParserControl (Parser char x) → ConstState char x
  control (Group parser) = lift (find parser)
  control (Alt a b) = lift (find a) *> lift (find b)
  control Empty = lift (pure unit)
  control (Label label parser) = lift $
    unlessM (State.gets (Map.member label)) do
      State.modify_ (Map.insert label (void parser))
      find parser

printLabelMap ∷ Map String BnfStmt → String
printLabelMap = intercalate "\n" <<< foldMapWithIndex \label bnf →
  [ label <> " = " <> printBnfStmt bnf <> ";\n" ]

printBnf ∷ ∀ char a. Parser char a → String
printBnf = findLabels >>> map toBnfStmt >>> printLabelMap
