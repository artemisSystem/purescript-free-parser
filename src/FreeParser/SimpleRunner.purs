module FreeParser.SimpleRunner where

import Prelude

import Control.Alt (class Alt, (<|>))
import Control.Alternative (class Alternative, empty)
import Control.Applicative.Free.Trans (runExists', runFree)
import Control.Lazy (class Lazy)
import Control.Plus (class Plus)
import Data.Array as Array
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Data.String (CodePoint)
import Data.String.CodePoints (singleton, uncons)
import Data.Tuple (Tuple(..))
import FreeParser (ManyF(..), OptionF(..), Parser, ParserBase(..), ParserControl(..))
import Leibniz (coerce')

newtype SimpleRunner str err a = SimpleRunner (str → Either err (Tuple str a))

derive instance Functor (SimpleRunner str err)

instance Apply (SimpleRunner str err) where
  apply (SimpleRunner pf) (SimpleRunner pa) = SimpleRunner \str → do
    Tuple str' f ← pf str
    Tuple str'' a ← pa str'
    pure (Tuple str'' (f a))

instance Applicative (SimpleRunner str err) where
  pure x = SimpleRunner \str → Right (Tuple str x)

instance Alt (SimpleRunner str err) where
  alt (SimpleRunner a) (SimpleRunner b) = SimpleRunner \str → a str <|> b str

instance Plus (SimpleRunner str String) where
  empty = SimpleRunner \_ → Left "No alternative"

instance Alternative (SimpleRunner str String)

instance Lazy (SimpleRunner str err a) where
  defer f = SimpleRunner \str → case f unit of SimpleRunner r → r str

parseString ∷ Parser CodePoint ~> SimpleRunner String String
parseString = runFree base control
  where
  base ∷ ParserBase CodePoint ~> SimpleRunner String String
  base (Satisfies tag pred proof) = SimpleRunner \str →
    case uncons str of
      Just { head, tail } →
        if pred head then Right $ Tuple tail (coerce' proof head)
        else Left $ "Expected " <> tag <> " but got " <> singleton head
      Nothing → Left $ "Expected " <> tag <> " but got end of file"
  base (Eof proof) = SimpleRunner \str → case uncons str of
    Just { head } → Left $ "Expected end of file but got " <> singleton head
    Nothing → Right $ Tuple "" (coerce' proof unit)
  base (Many ex) = runExists' ex \(ManyF parser proof) → coerce' proof <$>
    Array.many (parseString parser)
  base (Option ex) = runExists' ex \(OptionF parser proof) → coerce' proof <$>
    (Just <$> parseString parser <|> pure Nothing)

  control
    ∷ ∀ a
    . ParserControl (SimpleRunner String String a)
    → SimpleRunner String String a
  control (Label _ parser) = parser
  control (Group parser) = parser
  control Empty = empty
  control (Alt a b) = a <|> b
