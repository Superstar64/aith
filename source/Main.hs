module Main where

import Ast.Type hiding (Inline, kind, typeGlobalIdentifier, typeIdentifier, typex)
import qualified C.Ast as C
import qualified C.Print as C
import Codegen
import Control.Monad
import Control.Monad.Trans.State
import Data.Foldable
import Data.Functor.Identity (runIdentity)
import qualified Data.List as List
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Traversable (for)
import Misc.Path hiding (path)
import Module hiding (modulex)
import Simple
import Syntax hiding (Item (..))
import System.Console.GetOpt
import System.Directory
import System.Environment
import System.Exit
import System.FilePath
import Text.Megaparsec (SourcePos, errorBundlePretty)
import TypeCheck.Core
import Prelude hiding (readFile, writeFile)
import qualified Prelude

nameTypeLogical :: Applicative m => TypeLogical -> m TypeInfer
nameTypeLogical (TypeLogicalRaw i) = pure $ TypeAst () $ TypeSub $ TypeVariable $ TypeIdentifier $ show i

nameType :: TypeUnify -> TypeSource ()
nameType = sourceType . runIdentity . zonkType nameTypeLogical

prettyError :: TypeError [SourcePos] -> String
prettyError e = case e of
  TypeMismatch p σ σ' ->
    "Type mismatch between `" ++ pretty typex (nameType σ) ++ "` and `" ++ pretty typex (nameType σ') ++ "`" ++ positions p
  TypePolyMismatch p ς ς' ->
    prettyError
      (TypeMismatch p (TypeAst () $ Poly (TypeAst () AmbiguousLabel) ς) (TypeAst () $ Poly (TypeAst () AmbiguousLabel) ς'))
  TypeMisrelation p σ σ' ->
    "Unable to subtype `"
      ++ pretty typex (nameType (TypeAst () $ TypeSub σ'))
      ++ "` >= `"
      ++ pretty typex (nameType (TypeAst () $ TypeSub σ))
      ++ "`"
      ++ positions p
  ExpectedTypeAnnotation p -> "Expected type annotation: " ++ positions p
  AmbiguousType p σ -> "Ambiguous Type: `" ++ pretty typex (nameType $ flexible σ) ++ "`" ++ positions p
  UnknownGlobalIdentifier p x -> "Unknown Global: " ++ pretty termGlobalIdentifier x ++ positions p
  UnknownTypeGlobalIdentifier p x -> "Unknown Type Global: " ++ pretty typeGlobalIdentifier x ++ positions p
  TypeOccursCheck p v σ ->
    "Occurance Check: `" ++ pretty typex (nameType (TypeAst () $ TypeLogical v)) ++ "` in` " ++ pretty typex (nameType σ) ++ "`" ++ positions p
  EscapingSkolemType p x σ ->
    "Escaping Skolem: `" ++ pretty typeIdentifier x ++ "` in `" ++ pretty typex (nameType σ) ++ "`" ++ positions p
  NoCommonMeet p σ τ ->
    "No Common Meet between `" ++ pretty typex (nameType (TypeAst () $ TypeSub σ))
      ++ "` and `"
      ++ pretty typex (nameType (TypeAst () $ TypeSub τ))
      ++ "`"
      ++ positions p
  MismatchedTypeLambdas p -> "Mismatched type lambdas: " ++ positions p
  ExpectedPlainType p -> "Expected plain type: " ++ positions p
  IncorrectRegionBounds p -> "Incorrect Region Bounds: " ++ positions p
  NotTypable p -> "Not typable: " ++ positions p
  ExpectedSubtypable p -> "Expected subtypable: " ++ positions p
  ExpectedNewtype p σ -> "Expected Newtype: `" ++ pretty typex (nameType σ) ++ "`" ++ positions p

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

save :: String -> Item (GlobalSource ()) -> IO ()
save fileName item = writeFile fileName (pretty itemSingleton item)

loadModule fileName = do
  item <- load fileName
  case item of
    Module code -> pure code
    _ -> die $ fileName ++ " is not a module."

saveModule fileName code = save fileName (Module code)

addItems :: Module g -> [String] -> Module g -> IO (Module g)
addItems (CoreModule code) [] (CoreModule items) = pure $ CoreModule $ Map.union code items
addItems (CoreModule code) (name : path) items = do
  let inner = Map.findWithDefault (Module $ CoreModule $ Map.empty) name code
  case inner of
    Global _ -> die $ show name ++ " is not a module"
    Module inner -> do
      inner' <- addItems inner path items
      pure $ CoreModule $ Map.insert name (Module inner') code

addItem :: Module g -> Path -> Item g -> IO (Module g)
addItem code (Path heading name) item = addItems code heading $ CoreModule $ Map.singleton name item

addAll :: [([String], String)] -> IO (Module (GlobalSource SourcePos))
addAll = add <=< read
  where
    add = foldlM (uncurry . addItems) (CoreModule Map.empty)
    read = traverse (\(path, file) -> pure (,) <*> pure path <*> loadModule file)

pickItem :: Module.Module g -> [String] -> IO (Module.Item g)
pickItem code [] = pure $ Module code
pickItem (CoreModule items) [name] = case Map.lookup name items of
  Just item -> pure item
  Nothing -> die $ show name ++ " does not exist"
pickItem (CoreModule items) (first : remainder) = case Map.lookup first items of
  Just (Module code) -> pickItem code remainder
  _ -> die $ "unable to index module" ++ show first

formatItem :: Module (GlobalSource ()) -> [String] -> String -> IO ()
formatItem code path file = do
  item <- pickItem code path
  save file item

formatAll :: Module (GlobalSource ()) -> [([String], String)] -> IO ()
formatAll code = traverse_ (uncurry $ formatItem code)

compileModule :: Map TypeGlobalIdentifier TypeInfer -> Module (GlobalInfer p) -> [String] -> Dependency [C.Statement]
compileModule newtypes (CoreModule code) heading = concat <$> traverse (\(name, item) -> compileItem newtypes item (Path heading name)) (Map.toList code)

compileItem :: Map TypeGlobalIdentifier TypeInfer -> Item (GlobalInfer p) -> Path -> Dependency [C.Statement]
compileItem newtypes (Module items) (Path path name) = compileModule newtypes items (path ++ [name])
compileItem newtypes (Global (GlobalInfer (Text σ e))) path = do
  fn <- codegen (mangle path) (runSimplify (convertFunctionType σ) Map.empty newtypes) (runSimplify (convertFunction e) Map.empty newtypes)
  pure [fn]
compileItem _ (Global (GlobalInfer (Inline _ _))) _ = pure []
compileItem _ (Global (GlobalInfer (Synonym _))) _ = pure []
compileItem _ (Global (GlobalInfer (NewType _ _))) _ = pure []

newtypes :: Module (GlobalInfer p) -> Map TypeGlobalIdentifier TypeInfer
newtypes = Map.mapKeysMonotonic TypeGlobalIdentifier . flatten . mapMaybe new
  where
    new (GlobalInfer (NewType κ _)) = Just κ
    new _ = Nothing

generateItem code [] file = do
  let (functions, structs) = runDependency $ compileModule (newtypes code) code []
  writeFile file (C.emit C.code $ structs ++ functions)
generateItem code path file = do
  item <- pickItem code path
  let (functions, structs) = runDependency $ compileItem (newtypes code) item (Path (init path) (last path))
  writeFile file (C.emit C.code $ structs ++ functions)

generateAll code = traverse_ (uncurry $ generateItem code)

data CommandLine = CommandLine
  { loadItem :: [([String], FilePath)],
    prettyItem :: [([String], FilePath)],
    prettyItemAnnotated :: [([String], FilePath)],
    prettyItemReduced :: [([String], FilePath)],
    generateCItem :: [([String], FilePath)]
  }
  deriving (Show)

parsePathPair modify filePath targetPath cmd = case parseMaybe semiPath targetPath of
  Nothing -> die $ "Unable to parse path: " ++ targetPath
  Just path -> pure $ modify (path, filePath) cmd

loadCmd item command = command {loadItem = item : loadItem command}

formatCmd item command = command {prettyItem = item : prettyItem command}

annotateCmd item command = command {prettyItemAnnotated = item : prettyItemAnnotated command}

reduceCmd item command = command {prettyItemReduced = item : prettyItemReduced command}

cCmd item command = command {generateCItem = item : generateCItem command}

data Flags
  = Help
  | Load String
  | Output String
  | Wd String
  | Format
  | Annotate
  | Reduce
  | C
  deriving (Show, Eq)

descriptions =
  [ Option [] ["help"] (NoArg Help) "Help",
    Option ['d'] ["directory"] (ReqArg Wd "path") "Set",
    Option ['o'] ["output"] (ReqArg Output "file") "Output",
    Option ['F'] ["format"] (NoArg Format) "Format",
    Option ['A'] ["annotate"] (NoArg Annotate) "Annotate",
    Option ['R'] ["reduce"] (NoArg Reduce) "Reduce",
    Option ['C'] [] (NoArg C) "C"
  ]

printHelp = do
  putStrLn "Usage: aith [options] file..."
  putStrLn "Options:"
  putStrLn " -o<file>"
  putStrLn "     Set output file"
  putStrLn " -d<aith path>"
  putStrLn " --directory <aith path>"
  putStrLn "     Set the Aith path for the next command"
  putStrLn " -F"
  putStrLn " --format"
  putStrLn "     Format the output"
  putStrLn " -A"
  putStrLn " --annotate"
  putStrLn "     Annotate the outpt"
  putStrLn " -R"
  putStrLn " --reduce"
  putStrLn "     Reduce the output"
  putStrLn " -C"
  putStrLn "     Generate C into the output"
  exitSuccess

targets [] = [[]]
targets (x@(Load _) : xs) = [x] : targets xs
targets (x@(Output _) : xs) = [x] : targets xs
targets (x : xs) = (x : head remain) : tail remain
  where
    remain = targets xs

findLoad [] = []
findLoad (Load load : xs) = load : findLoad xs
findLoad (_ : xs) = findLoad xs

findOutput [] = []
findOutput (Output output : xs) = output : findOutput xs
findOutput (_ : xs) = findOutput xs

findWorking [] = []
findWorking (Wd wd : xs) = wd : findWorking xs
findWorking (_ : xs) = findWorking xs

countFormat = length . filter (== Format)

countAnnotate = length . filter (== Annotate)

countReduce = length . filter (== Reduce)

countC = length . filter (== C)

processCmd cmd [] = pure cmd
processCmd cmd t = case (findLoad t, findOutput t, working $ findWorking t, countFormat t, countAnnotate t, countReduce t, countC t) of
  ([file], [], Just wd, 0, 0, 0, 0) -> parsePathPair loadCmd file wd cmd
  ([], [file], Just wd, 1, 0, 0, 0) -> parsePathPair formatCmd file wd cmd
  ([], [file], Just wd, 0, 1, 0, 0) -> parsePathPair annotateCmd file wd cmd
  ([], [file], Just wd, 0, 0, 1, 0) -> parsePathPair reduceCmd file wd cmd
  ([], [file], Just wd, 0, 0, 0, 1) -> parsePathPair cCmd file wd cmd
  _ -> die $ "invalid flags" ++ show t
  where
    working [] = Just ""
    working [x] = Just x
    working _ = Nothing

baseMain command = do
  code <- addAll (loadItem command)
  code <- pure $ fmap (mapGlobalPosition (: [])) code
  formatAll (fmap (mapGlobalPosition (const ())) code) (prettyItem command)
  code <- handleModuleError $ order code
  code <- handleTypeError $ evalStateT (typeCheckModule code) emptyEnvironment

  formatAll (sourceGlobal <$> unorder code) (prettyItemAnnotated command)

  code <- pure $ reduceModule Map.empty code

  formatAll (sourceGlobal <$> unorder code) (prettyItemReduced command)
  generateAll (unorder code) (generateCItem command)
  where
    handleModuleError (Left e) = die $ prettyModuleError e
    handleModuleError (Right e) = pure e
    handleTypeError (Left e) = die $ prettyError e
    handleTypeError (Right e) = pure e

main' args = do
  let (flags, _, errors) = getOpt (ReturnInOrder Load) descriptions args
  case errors of
    [] -> case flags of
      [] -> printHelp
      _ -> case find (== Help) flags of
        Just _ -> printHelp
        _ -> do
          let options = targets flags
          cmd <- foldlM processCmd (CommandLine [] [] [] [] []) options
          baseMain cmd
    _ -> die $ List.intercalate "\n" errors

main = getArgs >>= main'
