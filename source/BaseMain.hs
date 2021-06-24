module BaseMain where

import qualified C.Ast as C
import qualified C.Print as C
import Codegen
import Core.Ast.Common
import qualified Data.Map as Map
import Data.Traversable (for)
import Error
import Misc.Identifier
import Misc.Path hiding (path)
import Module hiding (modulex)
import Syntax
import System.Directory
import System.Exit
import System.FilePath
import Text.Megaparsec (SourcePos, errorBundlePretty)
import Prelude hiding (readFile, writeFile)
import qualified Prelude

newtype PrettyIO a = PrettyIO {runPrettyIO :: IO a} deriving (Functor, Applicative, Monad)

quoted x = "\"" ++ x ++ "\""

prettyIdentifier (Identifier x) = quoted x

prettyType = quoted . pretty (typex Syntax.Runtime)

prettyKind = quoted . pretty kind

prettySort = quoted . pretty sort

prettyPath = quoted . pretty path

expected a b p = "Expected " ++ a ++ " but got " ++ b ++ positions p

prettyError (UnknownIdentfier p x) = "Unknown Identifier: " ++ prettyIdentifier x ++ positions p
prettyError (ExpectedMacro p σ) = expected "Macro" (prettyType σ) p
prettyError (ExpectedFunctionPointer p σ) = expected "Function" (prettyType σ) p
prettyError (ExpectedForall p σ) = expected "Forall" (prettyType σ) p
prettyError (ExpectedKindForall p σ) = expected "Kind Forall" (prettyType σ) p
prettyError (ExpectedQualified p σ) = expected "Qualified" (prettyType σ) p
prettyError (ExpectedOfCourse p σ) = expected "Of Course" (prettyType σ) p
prettyError (ExpectedRecursive p σ) = expected "Recursive" (prettyType σ) p
prettyError (ExpectedRegionTransformer p σ) = expected "Region Transformer" (prettyType σ) p
prettyError (ExpectedRegionReference p σ) = expected "Region Reference" (prettyType σ) p
prettyError (ExpectedType p κ) = expected "Type" (prettyKind κ) p
prettyError (ExpectedHigher p κ) = expected "Higher" (prettyKind κ) p
prettyError (ExpectedPoly p κ) = expected "Poly" (prettyKind κ) p
prettyError (ExpectedConstraint p κ) = expected "Constraint" (prettyKind κ) p
prettyError (ExpectedRegion p κ) = expected "Region" (prettyKind κ) p
prettyError (ExpectedText p κ) = expected "Text" (prettyKind κ) p
prettyError (ExpectedRuntime p κ) = expected "Runtime" (prettyKind κ) p
prettyError (ExpectedData p κ) = expected "Data" (prettyKind κ) p
prettyError (ExpectedReal p κ) = expected "Real" (prettyKind κ) p
prettyError (ExpectedKind p μ) = expected "Kind" (prettySort μ) p
prettyError (ExpectedStage p μ) = expected "Stage" (prettySort μ) p
prettyError (ExpectedImpact p μ) = expected "Impact" (prettySort μ) p
prettyError (ExpectedExistance p μ) = expected "Existance" (prettySort μ) p
prettyError (ExpectedRepresentation p μ) = expected "Representation" (prettySort μ) p
prettyError (EscapingTypeVariable p α σ) = "Escaping type variable " ++ prettyIdentifier α ++ " " ++ prettyType σ ++ positions p
prettyError (IncompatibleType p σ τ) = "Type mismatch between " ++ prettyType σ ++ " and " ++ prettyType τ ++ positions p
prettyError (IncompatibleKind p κ κ') = "Kind mismatch between " ++ prettyKind κ ++ " and " ++ prettyKind κ' ++ positions p
prettyError (IncompatibleSort p μ μ') = "Sort mismatch between " ++ prettySort μ ++ " and " ++ prettySort μ' ++ positions p
prettyError (CaptureLinear p x) = "Linear variable " ++ prettyIdentifier x ++ " captured" ++ positions p
prettyError (InvalidUsage p x) = "Linear Variable " ++ prettyIdentifier x ++ " copied" ++ positions p
prettyError (NoProof p σ) = "No proof for " ++ prettyType σ ++ positions p

prettyModuleError (IllegalPath p path) = "Unknown path " ++ prettyPath path ++ positions p
prettyModuleError (IncompletePath p path) = "Incomplete path " ++ prettyPath path ++ positions p
prettyModuleError (IndexingGlobal p path) = "Indexing global declaration" ++ prettyPath path ++ positions p
prettyModuleError (Cycle p path) = "Global cycle" ++ prettyPath path ++ positions p

positions p = " in positions: " ++ show p

instance Base [SourcePos] PrettyIO where
  quit e = PrettyIO $ die $ prettyError e
  moduleQuit e = PrettyIO $ die $ prettyModuleError e

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
  writeFile file (C.emit C.globals $ structs ++ functions)

baseMain arguments = do
  case arguments of
    [] -> printHelp
    _ -> pure ()
  command <- parseArguments arguments
  code <- (fmap (: [])) <$> addAll (loadItem command) :: IO (Module [SourcePos])
  prettyAll (prettyItem command) (Internal <$ code)
  ordering <- runPrettyIO $ order code
  environment <- runPrettyIO $ typeCheckModule ordering
  let code = unorder $ reduceModule environment ordering
  prettyAll (prettyItemReduced command) (Internal <$ code)
  generateAll (generateCItem command) (Internal <$ code)
