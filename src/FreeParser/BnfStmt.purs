module FreeParser.BnfStmt where

import Prelude

import Control.Applicative.Free.Trans (foldFree, runExists')
import Data.Foldable (intercalate)
import Data.Generic.Rep (class Generic)
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
  base (Option ex) = runExists' ex \(OptionF parser _) → BnfOption
    (toBnfStmt parser)

  control ∷ ParserControl BnfStmt → BnfStmt
  control (Label str _) = BnfReference str
  control (Group stmt) = BnfParens stmt
  control (Alt a b) = AltBnf a b
  control Empty = mempty
