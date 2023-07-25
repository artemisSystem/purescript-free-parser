module FreeParser where

import Prelude

import Control.Alternative.Free (FreeAlt, liftF, matchFree)
import Control.Applicative.Free.Trans (runExists')
import Data.Const (Const(..))
import Data.Exists (Exists, mkExists)
import Data.Maybe (Maybe)
import Data.Newtype (un)
import Data.String.CodeUnits (fromCharArray, toCharArray)
import Data.Traversable (intercalate, traverse)
import Leibniz (type (~))

data TaggedFunction a b = TaggedFunction String (a → b)

infix 4 type TaggedFunction as -*>

run ∷ ∀ a b. (a -*> b) → (a → b)
run (TaggedFunction _ f) = f

data ManyF char a b = ManyF (Parser char b) (a ~ Array b)
data OptionF char a b = OptionF (Parser char b) (a ~ Maybe b)

data ParserF char a
  = Label String (Parser char a)
  | Group (Parser char a)
  | Eof (a ~ Unit)
  | Satisfies (char -*> Boolean) (a ~ char)
  | Many (Exists (ManyF char a))
  | Option (Exists (OptionF char a))

type Parser char = FreeAlt (ParserF char)

label ∷ ∀ char a. String → Parser char a → Parser char a
label str parser = liftF (Label str parser)

group ∷ ∀ char a. Parser char a → Parser char a
group parser = liftF (Group parser)

eof ∷ ∀ char. Parser char Unit
eof = liftF (Eof identity)

satisfies ∷ ∀ char. (char -*> Boolean) → Parser char char
satisfies pred = liftF (Satisfies pred identity)

many ∷ ∀ char a. Parser char a → Parser char (Array a)
many parser = liftF $ Many $ mkExists (ManyF parser identity)

option ∷ ∀ char a. Parser char a → Parser char (Maybe a)
option parser = liftF $ Option $ mkExists (OptionF parser identity)

literal ∷ ∀ char. Eq char ⇒ Show char ⇒ char → Parser char char
literal char = satisfies (TaggedFunction (show char) (_ == char))

string ∷ String → Parser Char String
string = toCharArray >>> traverse literal >>> map fromCharArray

manySpace ∷ Parser Char String
manySpace = fromCharArray <$> many (satisfies $ TaggedFunction "space" isSpace)
  where
  isSpace c = c == '\n' || c == '\r' || c == ' ' || c == '\t'

printBnf ∷ ∀ char a. Parser char a → String
printBnf = un Const <<< matchFree
  ( \f fs → Const $ printSingle f <> case fs of
      (Const "") → ""
      (Const x) → ", " <> x
  )
  (\_ → Const "")
  (intercalate (Const " | "))

  where
  printSingle ∷ ∀ x. ParserF char x → String
  printSingle (Label str _) = str
  printSingle (Group parser) = "(" <> printBnf parser <> ")"
  printSingle (Eof _) = "EoF"
  printSingle (Satisfies (TaggedFunction str _) _) = "\"" <> str <> "\""
  printSingle (Many ex) = runExists' ex \(ManyF parser _) →
    "{" <> printBnf parser <> "}"
  printSingle (Option ex) = runExists' ex \(OptionF parser _) →
    "[" <> printBnf parser <> "]"
