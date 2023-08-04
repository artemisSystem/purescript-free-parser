module FreeParser where

import Prelude

import Control.Alternative.Free (liftF)
import Control.Applicative.Free.Trans (class LiftAlt, FreeAT, wrap)
import Data.CodePoint.Unicode (isSpace)
import Data.Exists (Exists, mkExists)
import Data.Lazy (Lazy, defer)
import Data.Maybe (Maybe(..))
import Data.String.CodePoints (CodePoint, fromCodePointArray, singleton, toCodePointArray)
import Data.Traversable (traverse)
import Leibniz (type (~))

data ParserControl a
  = Label String (Lazy a)
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
  = Eof a
  | Parse String (char → Maybe a)
  | Many (Exists (ManyF char a))
  | Option (Exists (OptionF char a))

type Parser char = FreeAT (ParserBase char) ParserControl

label ∷ ∀ char a. String → (Unit → Parser char a) → Parser char a
label str parser = wrap (Label str (defer parser))

group ∷ ∀ char a. Parser char a → Parser char a
group parser = wrap (Group parser)

eof ∷ ∀ char. Parser char Unit
eof = liftF (Eof unit)

parse ∷ ∀ char a. String → (char → Maybe a) → Parser char a
parse tag f = liftF (Parse tag f)

satisfies ∷ ∀ char. String → (char → Boolean) → Parser char char
satisfies tag pred = parse tag \char → if pred char then Just char else Nothing

many ∷ ∀ char a. Parser char a → Parser char (Array a)
many parser = liftF $ Many $ mkExists (ManyF parser identity)

manyChar ∷ ∀ char. Parser char CodePoint → Parser char String
manyChar parser = fromCodePointArray <$> many parser

option ∷ ∀ char a. Parser char a → Parser char (Maybe a)
option parser = liftF $ Option $ mkExists (OptionF parser identity)

literal ∷ CodePoint → Parser CodePoint CodePoint
literal char = satisfies (singleton char) (_ == char)

string ∷ String → Parser CodePoint String
string = toCodePointArray >>> traverse literal >>> map fromCodePointArray

manySpace ∷ Parser CodePoint String
manySpace = manyChar (satisfies "space" isSpace)
