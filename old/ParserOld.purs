module ParserOld where

import Prelude

import Data.Either (Either(..))
import Data.Exists (Exists, runExists)
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))
import Leibniz (type (~), coerce')

data TaggedFunction a b = TaggedFunction String (a → b)

infix 4 type TaggedFunction as -*>

data ParseError = ParseError

data BasicParser char
  = Match char
  | Range char char
  | Predicate (char -*> Boolean)

parseBasic ∷ ∀ char. Ord char ⇒ BasicParser char → char → Either ParseError char
parseBasic (Match a) = \b → if a == b then Right b else Left ParseError
parseBasic (Range from to) = \char →
  if between from to char then Right char else Left ParseError
parseBasic (Predicate (TaggedFunction _tag pred)) = \char →
  if pred char then Right char else Left ParseError

data MapF str char a b = MapF (b → a) (Parser str char b)

data Parser str char a
  = Basic (BasicParser char) (a ~ char)
  | Alt (Parser str char a) (Parser str char a)
  | Empty ParseError
  | Map (Exists (MapF str char a))

data TaggedParser

type ParserOptions str char =
  { uncons ∷ (str → Maybe (Tuple str char))
  , choose ∷ ∀ a. Parser str char a → Parser str char a → Parser str char a
  }

-- parse
--   ∷ ∀ str char a
--   . Ord char
--   ⇒ ParserOptions str char
--   → Parser str char a
--   → (str → Either ParseError (Tuple str a))
-- parse { uncons } (Basic parser proof) = \str → case uncons str of
--   Nothing → Left ParseError
--   Just (Tuple str char) → parseBasic parser char <#> \c →
--     Tuple str (coerce' proof c)
-- parse opts@{ choose } (Alt a b) = \str → choose (parse opts a str)
--   (parse opts b str)
-- parse _ (Empty err) = \_ → Left err
-- parse opts (Map ex) = ex # runExists
--   \(MapF f parser) → (map <<< map <<< map) f (parse opts parser)

-- newtype NormalParser str char a = NormalParser (str → (Either ParseError (Tuple str a)))