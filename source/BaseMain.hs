module BaseMain where

import qualified C.Ast as C
import qualified C.Print as C
import Codegen
import Core.Ast.Common
import qualified Data.Map as Map
import Data.Traversable (for)
import Misc.Identifier
import Misc.Path hiding (path)
import Misc.Syntax
import Module hiding (modulex)
import Syntax
import System.Directory
import System.Exit
import System.FilePath
import Text.Megaparsec (SourcePos, errorBundlePretty)
import Prelude hiding (readFile, writeFile)
import qualified Prelude

readFile "-" = getContents
readFile name = do
  file <- Prelude.readFile name
  pure $ length file `seq` file -- stop lazy io

writeFile "-" file = putStrLn file
writeFile name file = Prelude.writeFile name file

data CommandLine = CommandLine
  { loadItem :: [(Path, FilePath)],
    prettyItem :: [(Path, FilePath)],
    prettyItemReduced :: [(Path, FilePath)],
    generateCItem :: [(Path, FilePath)]
  }

printHelp = do
  putStrLn "Usage: aith [options]"
  putStrLn "Options:"
  putStrLn " --load <file> <aith path>"
  putStrLn "     Load a file or folder into the specified aith path"
  putStrLn " --format <aith path> <file>"
  putStrLn "     Format the specified aith path into a file"
  putStrLn " --reduce <aith path> <file>"
  putStrLn "     Reduce and format the specified aith path into a file"
  putStrLn " --generate-c <aith path> <file>"
  putStrLn "     Generate C source from the specified path into a file"
  exitSuccess

parsePathPair modify filePath targetPath xs = case parseMaybe path targetPath of
  Nothing -> die $ "Unable to parse path: " ++ targetPath
  Just path -> modify (path, filePath) <$> parseArguments xs

parseArguments ("--help" : _) = printHelp
parseArguments ("--load" : filePath : targetPath : xs) = parsePathPair load filePath targetPath xs
  where
    load item command = command {loadItem = item : loadItem command}
parseArguments ("--format" : targetPath : filePath : xs) = parsePathPair pretty filePath targetPath xs
  where
    pretty item command = command {prettyItem = item : prettyItem command}
parseArguments ("--reduce" : targetPath : filePath : xs) = parsePathPair pretty filePath targetPath xs
  where
    pretty item command = command {prettyItemReduced = item : prettyItem command}
parseArguments ("--generate-c" : targetPath : filePath : xs) = parsePathPair generate filePath targetPath xs
  where
    generate item command = command {generateCItem = item : generateCItem command}
parseArguments [] = pure $ CommandLine [] [] [] []
parseArguments x = die $ "Unknown arguments" ++ show x

load fileName = do
  isDirectory <- doesDirectoryExist fileName
  if isDirectory
    then do
      children <- listDirectory fileName
      inner <- for children $ \child -> do
        item <- load (fileName ++ [pathSeparator] ++ child)
        pure (Identifier (dropExtension child), item)
      pure (Module $ CoreModule $ Map.fromList inner)
    else do
      file <- readFile fileName
      case parse itemSingleton fileName file of
        Right x -> pure x
        Left e -> die $ errorBundlePretty e

addItem (Path [] name) item (CoreModule items) = pure $ CoreModule $ Map.insert name item items
addItem (Path (first : remainder) name) item (CoreModule items) = do
  let inner = Map.findWithDefault (Module $ CoreModule $ Map.empty) first items
  case inner of
    Global _ -> die $ show name ++ " is not a module"
    Module inner -> do
      inner' <- addItem (Path remainder name) item inner
      pure $ CoreModule $ Map.insert first (Module inner') items

addAll [] = pure $ CoreModule Map.empty
addAll ((path, file) : xs) = do
  tail <- addAll xs
  item <- load file
  addItem path item tail

pickItem (Path [] name) (CoreModule items) = case Map.lookup name items of
  Just item -> pure item
  Nothing -> die $ show name ++ " does not exist"
pickItem (Path (first : remainder) name) (CoreModule items) = case Map.lookup first items of
  Just (Module code) -> pickItem (Path remainder name) code
  _ -> die $ "unable to index module" ++ show first

prettyAll [] _ = pure ()
prettyAll ((path, file) : remainder) code = do
  prettyAll remainder code
  item <- pickItem path code
  writeFile file (pretty itemSingleton item)

generateAll [] _ = pure ()
generateAll ((path@(Path heading name), file) : remainder) code = do
  generateAll remainder code
  item <- pickItem path code
  let (functions, structs) = C.escapeStructs $ compileItem heading name item
  writeFile file (pretty C.globals $ structs ++ functions)

baseMain arguments = do
  case arguments of
    [] -> printHelp
    _ -> pure ()
  command <- parseArguments arguments
  code <- (fmap (: [])) <$> addAll (loadItem command) :: IO (Module [SourcePos])
  prettyAll (prettyItem command) (Internal <$ code)
  ordering <- order code
  environment <- typeCheckModule ordering
  let code = unorder $ reduceModule environment ordering
  prettyAll (prettyItemReduced command) (Internal <$ code)
  generateAll (generateCItem command) (Internal <$ code)
