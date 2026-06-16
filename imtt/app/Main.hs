{-# LANGUAGE OrPatterns #-}

module Main where

import System.Console.Haskeline qualified as Haskeline
import Data.Function (fix)

main :: IO ()
main = Haskeline.runInputT Haskeline.defaultSettings $ fix \loop ->
  Haskeline.getInputLine "> " >>= \case
    (Nothing; Just "quit") -> pure ()
    Just _ -> loop
