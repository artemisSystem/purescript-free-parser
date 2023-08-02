module FreeParser where

import Prelude

import Control.Alternative.Free (liftF)
import Control.Applicative.Free.Trans (class LiftAlt, FreeAT, wrap)
import Data.Exists (Exists, mkExists)
import Data.Maybe (Maybe)
import Data.String.CodeUnits (fromCharArray, singleton, toCharArray)
import Data.Traversable (traverse)
import Leibniz (type (~))

data TaggedFunction a b = TaggedFunction String (a → b)

infix 4 type TaggedFunction as -*>

run ∷ ∀ a b. (a -*> b) → (a → b)
run (TaggedFunction _ f) = f

data ParserControl a
  = Label String a
  | Group a
  | Empty
  | Alt a a

derive instance Functor ParserControl

instance LiftAlt ParserControl where
  liftAlt a b = Alt a b
  empty' = Empty

data ManyF char a b = ManyF (Parser char b) (a ~ Array b)
data OptionF char a b = OptionF (Parser char b) (a ~ Maybe b)

data ParserBase char a
  = Eof (a ~ Unit)
  | Satisfies (char -*> Boolean) (a ~ char)
  | Many (Exists (ManyF char a))
  | Option (Exists (OptionF char a))

type Parser char = FreeAT (ParserBase char) ParserControl

label ∷ ∀ char a. String → Parser char a → Parser char a
label str parser = wrap (Label str parser)

group ∷ ∀ char a. Parser char a → Parser char a
group parser = wrap (Group parser)

eof ∷ ∀ char. Parser char Unit
eof = liftF (Eof identity)

satisfies ∷ ∀ char. (char -*> Boolean) → Parser char char
satisfies pred = liftF (Satisfies pred identity)

many ∷ ∀ char a. Parser char a → Parser char (Array a)
many parser = liftF $ Many $ mkExists (ManyF parser identity)

option ∷ ∀ char a. Parser char a → Parser char (Maybe a)
option parser = liftF $ Option $ mkExists (OptionF parser identity)

literal ∷ Char → Parser Char Char
literal char = satisfies (TaggedFunction (singleton char) (_ == char))

string ∷ String → Parser Char String
string = toCharArray >>> traverse literal >>> map fromCharArray

manySpace ∷ Parser Char String
manySpace = fromCharArray <$> many (satisfies $ TaggedFunction "space" isSpace)
  where
  isSpace c = c == '\n' || c == '\r' || c == ' ' || c == '\t'
