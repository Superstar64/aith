module Main where

import Ast.Common
import Ast.Kind hiding (typex)
import Ast.Term
import Ast.Type hiding (Inline)
import qualified C.Ast as C
import qualified C.Print as C
import Codegen
import Data.Functor.Identity (runIdentity)
import qualified Data.Map as Map
import Data.Traversable (for)
import Misc.Path hiding (path)
import Module hiding (modulex)
import Simple
import Syntax
import System.Directory
import System.Environment
import System.Exit
import System.FilePath
import Text.Megaparsec (SourcePos, errorBundlePretty)
import TypeCheck.Core
import Prelude hiding (readFile, writeFile)
import qualified Prelude

nameTypeLogical :: Applicative m => TypeLogical -> m TypeInfer
nameTypeLogical (TypeLogicalRaw i) = pure $ TypeCore $ TypeVariable $ TypeIdentifier $ show i

nameKindLogical :: Applicative m => KindLogical -> m KindInfer
nameKindLogical (KindLogicalRaw i) = pure $ KindCore $ KindVariable $ KindIdentifier $ show i

nameType :: TypeUnify -> TypeSource Internal
nameType = sourceType . runIdentity . zonkType nameTypeLogical . runIdentity . zonkKind nameKindLogical

nameKind :: KindUnify -> KindSource Internal
nameKind = sourceKind . runIdentity . zonkKind nameKindLogical

prettyError :: TypeError [SourcePos] -> String
prettyError (UnknownIdentifier p (TermIdentifier x)) = "Unknown identifer " ++ x ++ positions p
prettyError (TypeMismatch p σ σ') = "Type mismatch between ``" ++ pretty typex (nameType σ) ++ "`` and ``" ++ pretty typex (nameType σ') ++ "``" ++ positions p
prettyError (KindMismatch p κ κ') = "Kind mismatch between ``" ++ pretty kind (nameKind κ) ++ "`` and ``" ++ pretty kind (nameKind κ') ++ "``" ++ positions p
prettyError (ConstraintMismatch p c σ) = "Unable to proof ``" ++ pretty constraint c ++ "(" ++ pretty typex (nameType σ) ++ ")``" ++ positions p
prettyError e = show e

quoted x = "\"" ++ x ++ "\""

prettyIdentifier x = quoted x

prettyPath = quoted . pretty path

expected a b p = "Expected " ++ a ++ " but got " ++ b ++ positions p

prettyModuleError (IllegalPath p path) = "Unknown path " ++ prettyPath path ++ positions p
prettyModuleError (IncompletePath p path) = "Incomplete path " ++ prettyPath path ++ positions p
prettyModuleError (IndexingGlobal p path) = "Indexing global declaration" ++ prettyPath path ++ positions p
prettyModuleError (Cycle p path) = "Global cycle" ++ prettyPath path ++ positions p

positions p = " in positions: " ++ show p

readFile "-" = getContents
readFile name = do
  file <- Prelude.readFile name
  pure $ length file `seq` file -- stop lazy io

writeFile "-" file = putStrLn file
writeFile name file = Prelude.writeFile name file

data CommandLine = CommandLine
  { loadItem :: [(Path, FilePath)],
    prettyItem :: [(Path, FilePath)],
    prettyItemAnnotated :: [(Path, FilePath)],
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
  putStrLn " --annotate <aith path> <file>"
  putStrLn "     Annotate and format the specified aith path into a file"
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
parseArguments ("--annotate" : targetPath : filePath : xs) = parsePathPair pretty filePath targetPath xs
  where
    pretty item command = command {prettyItemAnnotated = item : prettyItemAnnotated command}
parseArguments ("--reduce" : targetPath : filePath : xs) = parsePathPair pretty filePath targetPath xs
  where
    pretty item command = command {prettyItemReduced = item : prettyItemReduced command}
parseArguments ("--generate-c" : targetPath : filePath : xs) = parsePathPair generate filePath targetPath xs
  where
    generate item command = command {generateCItem = item : generateCItem command}
parseArguments [] = pure $ CommandLine [] [] [] [] []
parseArguments x = die $ "Unknown arguments" ++ show x

load :: String -> IO (Item (GlobalSource SourcePos))
load fileName = do
  isDirectory <- doesDirectoryExist fileName
  if isDirectory
    then do
      children <- listDirectory fileName
      inner <- for children $ \child -> do
        item <- load (fileName ++ [pathSeparator] ++ child)
        pure (dropExtension child, item)
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

prettyAll :: [(Path, String)] -> Module (GlobalSource Internal) -> IO ()
prettyAll [] _ = pure ()
prettyAll ((path, file) : remainder) code = do
  prettyAll remainder code
  item <- pickItem path code
  writeFile file (pretty itemSingleton item)

compileFunctionLiteral ::
  [String] ->
  String ->
  TypeSchemeInfer ->
  TermSchemeInfer p ->
  Dependency (C.Statement)
compileFunctionLiteral path name σ e = codegen sym (simpleFunctionType σ) (simpleFunction e)
  where
    sym = mangle (Path path name)

compileModule :: [String] -> Module (GlobalInfer p) -> Dependency [C.Statement]
compileModule path (CoreModule code) = concat <$> traverse (uncurry (compileItem path)) (Map.toList code)

compileItem ::
  [String] ->
  String ->
  Item (GlobalInfer p) ->
  Dependency [C.Statement]
compileItem path name (Module items) = compileModule (path ++ [name]) items
compileItem path name (Global (GlobalInfer (Text σ e))) = pure (:) <*> compileFunctionLiteral path name σ e <*> pure []
compileItem _ _ (Global (GlobalInfer (Inline _ _))) = pure []
compileItem _ _ (Global (GlobalInfer (Import _ _))) = pure []

generateAll [] _ = pure ()
generateAll ((path@(Path heading name), file) : remainder) code = do
  generateAll remainder code
  item <- pickItem path code
  let (functions, structs) = runDependency $ compileItem heading name item
  writeFile file (C.emit C.code $ structs ++ functions)

uninfer :: ModuleOrder (GlobalInfer [SourcePos]) -> ModuleOrder (GlobalSource Internal)
uninfer = fmap nameGlobal
  where
    nameGlobal :: GlobalInfer [SourcePos] -> GlobalSource Internal
    nameGlobal (GlobalInfer (Inline ς e)) = GlobalSource $ Inline (Just $ sourceTypeScheme ς) (sourceTermScheme e)
    nameGlobal (GlobalInfer (Text ς e)) = GlobalSource $ Text (Just $ sourceTypeScheme ς) (sourceTermScheme e)
    nameGlobal (GlobalInfer (Import _ path)) = GlobalSource $ Import Internal path

baseMain arguments = do
  case arguments of
    [] -> printHelp
    _ -> pure ()
  command <- parseArguments arguments
  code <- fmap (fmap (: [])) <$> addAll (loadItem command) :: IO (Module (GlobalSource [SourcePos]))
  prettyAll (prettyItem command) (fmap (fmap (const Internal)) code)
  ordering <- handleModuleError $ order code
  ordering' <- handleTypeError $ typeCheckModule ordering
  let code' = unorder $ uninfer $ ordering'
  prettyAll (prettyItemAnnotated command) code'
  let ordering'' = reduceModule ordering'
  let code'' = unorder $ uninfer $ ordering''
  prettyAll (prettyItemReduced command) code''
  generateAll (generateCItem command) (unorder $ ordering'')
  where
    handleModuleError (Left e) = die $ prettyModuleError e
    handleModuleError (Right e) = pure e
    handleTypeError (Left e) = die $ prettyError e
    handleTypeError (Right e) = pure e

main = do
  args <- getArgs
  baseMain args
