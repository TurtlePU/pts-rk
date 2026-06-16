{-# LANGUAGE OrPatterns #-}

module Main where

import Control.Exception qualified as Exception
import Control.Monad qualified as Monad
import Control.Monad.IO.Class qualified as IO
import Core qualified
import Data.Foldable qualified as Foldable
import Data.IORef qualified as IORef
import Data.Set qualified as Set
import Source qualified as Source
import System.Console.Haskeline qualified as Haskeline
import System.Exit qualified as System

data ReplError = OnParse Source.ParseError | OnName Core.NameResolutionError
  deriving Show

instance Exception.Exception ReplError

class ToReplError a where
  toReplError :: a -> ReplError

instance ToReplError Source.ParseError where
  toReplError = OnParse

instance ToReplError Core.NameResolutionError where
  toReplError = OnName

throwRepl :: (IO.MonadIO m, ToReplError e) => e -> m a
throwRepl = IO.liftIO . Exception.throwIO . toReplError

repl :: Haskeline.InputT IO () -> IO ()
repl iter =
  Haskeline.runInputT Haskeline.defaultSettings
  $ Monad.forever
  $ Haskeline.withRunInBase \lift ->
    Exception.catch (lift iter) (lift . Haskeline.outputStrLn . show @ReplError)

main :: IO ()
main = IORef.newIORef Set.empty >>= \globals -> repl do
  input <- Haskeline.getInputLine "> " >>= \case
    (Nothing; Just "quit") -> IO.liftIO System.exitSuccess
    Just input -> pure input
  command <- Source.parseReplCommand throwRepl input
  defined <- flip Set.member <$> IO.liftIO (IORef.readIORef globals)
  resolved <- Core.resolveNames throwRepl defined (Source.getTerm command)
  Foldable.for_ (Source.getName command) $
    IO.liftIO . IORef.modifyIORef' globals . Set.insert
  Haskeline.outputStrLn (show resolved)
