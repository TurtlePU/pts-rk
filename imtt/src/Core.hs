{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ViewPatterns #-}

module Core where

import Control.Monad.Trans.Reader (ReaderT (..))
import Control.Selective (Validation (..))
import Data.List (elemIndex)
import Data.List.NonEmpty (NonEmpty (..), toList)
import Source (Name (nameText), SourceTerm (..), Intro (..))
import qualified Data.Text as Text

newtype Index = MkIndex { indexInt :: Int } deriving newtype Show

data Projection = Fst | Snd deriving Show

data CoreTerm
  = TPi (Maybe Name) CoreTerm CoreTerm
  | TAbs (Maybe Name) CoreTerm CoreTerm
  | TApp CoreTerm CoreTerm
  | TSig (Maybe Name) CoreTerm CoreTerm
  | TPair CoreTerm CoreTerm
  | TProj Projection
  | TVar (Either Name Index)
  | TAscr CoreTerm CoreTerm
  | THole
  deriving Show

newtype CatList a = MkCatList { runCatList :: [a] -> NonEmpty a }

instance Semigroup (CatList a) where
  MkCatList f <> MkCatList g = MkCatList (f . toList . g)

newtype NameResolutionError = MkNRE (NonEmpty Name)

instance Show NameResolutionError where
  show (MkNRE (fmap nameText -> names)) =
    Text.unpack $ "Unresolved names: " <> Text.intercalate ", " (toList names)

resolveNames ::
  Applicative f =>
  (forall a. NameResolutionError -> f a) ->
  (Name -> Bool) -> SourceTerm -> f CoreTerm
resolveNames throw global st = case runReaderT (s2c st) [] of
  Failure e -> throw $ MkNRE (runCatList e [])
  Success a -> pure a
 where
  ctxExtend n m = ReaderT \local -> runReaderT m (n : local)
  s2c = \case
    Pi (MkIntro n s) t -> TPi (Just n) <$> s2c s <*> ctxExtend n (s2c t)
    Abs (MkIntro n s) t -> TAbs (Just n) <$> s2c s <*> ctxExtend n (s2c t)
    App s t -> TApp <$> s2c s <*> s2c t
    Sig (MkIntro n s) t -> TSig (Just n) <$> s2c s <*> ctxExtend n (s2c t)
    Pair s t -> TPair <$> s2c s <*> s2c t
    Var n -> TVar <$> ReaderT \local -> case elemIndex n local of
      Just i -> pure $ Right (MkIndex i)
      Nothing -> if global n then pure (Left n) else Failure (MkCatList (n :|))
    Ascr s t -> TAscr <$> s2c s <*> s2c t
    Hole -> pure THole
