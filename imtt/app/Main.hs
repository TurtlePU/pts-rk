{-# LANGUAGE OrPatterns #-}

module Main where

import System.Console.Haskeline qualified as Haskeline
import Data.Function (fix)
import Source (parseReplCommand)
import Control.Monad.IO.Class (liftIO)

main :: IO ()
main = Haskeline.runInputT Haskeline.defaultSettings $ fix \loop ->
  Haskeline.getInputLine "> " >>= \case
    (Nothing; Just "quit") -> pure ()
    Just input -> liftIO (either putStr print $ parseReplCommand input) >> loop
