module Main where

import Frames
import Invariants

import Data.List
import Data.Either
import Control.Monad.Error
import System.Environment
import System.IO
import System.Directory
import System.FilePath
import Language.Eiffel.Parser.Parser
import Language.Eiffel.PrettyPrint

defaultOutDir = "modified"

-- | Read input directory from the first argument and output processed class files or errors into defaultOutDir
main = do
  dir:_ <- getArgs
  files <- filesWithExt "e" dir
  createDirectoryIfMissing True (defaultOutDir)
  classes <- mapM parseClassFile files
  zipWithM (go dir (rights classes)) files classes
  where
    go dir classes file clsE = do
      h <- openFile (outFile dir file) WriteMode
      case clsE of
        Left err -> hPrint h err
        Right cls -> do
          clsE' <- runErrorT (foldM (flip ($)) cls 
            [
              addFrames classes
            , processInvariants classes
            ])
          case clsE' of
            Left err -> hPrint h err
            Right cls' -> hPutStr h (renderWithTabs (toDoc cls'))
      hClose h
    outFile dir file = defaultOutDir </> takeFileName file
    processingSteps classes = map ($ classes) [addFrames, processInvariants]
    
-- | List of files with extension ext located (recursively) in path
filesWithExt :: String -> FilePath -> IO [FilePath]
filesWithExt ext path = do
  isDir <- doesDirectoryExist path
  if isDir 
    then do
      content <- getDirectoryContents path
      results <- mapM (filesWithExt ext) (map (combine path) (content \\ relativePaths))
      return $ concat results
    else if snd (splitExtension path) == '.':ext
      then return [path]
      else return []
  where
    relativePaths = [".", ".."]
    