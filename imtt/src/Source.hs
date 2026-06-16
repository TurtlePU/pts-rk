module Source where

import Control.Applicative (Alternative (..), asum, (<**>))
import Data.Bifunctor (first)
import Data.Char qualified as Char
import Data.Text (Text)
import Data.Text qualified as Text
import Data.Void (Void)
import Text.Megaparsec (MonadParsec (..), sepBy1)
import Text.Megaparsec qualified as Megaparsec
import Text.Megaparsec.Char qualified as Char
import Text.Megaparsec.Char.Lexer qualified as Lexer

newtype Name = MkName { nameText :: Text } deriving newtype Show

data Intro = MkIntro !Name !SourceTerm deriving Show

data SourceTerm
  = Pi !Intro !SourceTerm
  | Abs !Intro !SourceTerm
  | App !SourceTerm !SourceTerm
  | Sig !Intro !SourceTerm
  | Pair !SourceTerm !SourceTerm
  | Var !Name
  | Ascr !SourceTerm !SourceTerm
  | Hole
  deriving Show

data ReplCommand = Eval !SourceTerm | Def !Name !SourceTerm deriving Show

type Parsec = Megaparsec.Parsec Void String

space :: Parsec ()
space = Lexer.space Char.space1 empty empty

symbol :: String -> Parsec String
symbol = Lexer.symbol space

parens :: Parsec a -> Parsec a
parens = Megaparsec.between (symbol "(") (symbol ")")

name :: Parsec Name
name = Lexer.lexeme space $ MkName . Text.pack <$>
  ((:) <$> Char.letterChar <*> takeWhile1P (Just "alphanum") Char.isAlphaNum)

intro :: Parsec Intro
intro =
  parens (MkIntro <$> name <* symbol ":" <*> term)
  <|> (`MkIntro` Hole) <$> name

term :: Parsec SourceTerm
term = foldr1 Ascr <$> (`sepBy1` symbol ":") (
    foldl1 App <$> some (
      foldr1 Pair <$> parens (term `sepBy1` symbol ",")
      <|> symbol "_" *> pure Hole
      <|> Var <$> name
      <|> asum [
        symbol s *> some intro <* symbol "." <**> fmap (foldr f) term
        | (s, f) <- [("*", Pi), ("\\", Abs), ("+", Sig)]
      ]
    )
  )

replCommand :: Parsec ReplCommand
replCommand = Megaparsec.between space eof $ asum
  [ try $ Def <$> name <* symbol ":=" <*> term
  , Eval <$> term
  ]

parseReplCommand :: String -> Either String ReplCommand
parseReplCommand =
  first Megaparsec.errorBundlePretty
  . Megaparsec.parse @Void replCommand "repl"
