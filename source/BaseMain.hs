module BaseMain where

import Ast.Common
import Ast.Kind hiding (typex)
import Ast.Term
import Ast.Type hiding (Inline)
import qualified C.Ast as C
import qualified C.Print as C
import Codegen
import Control.Monad.Reader
import Data.Bifunctor
import qualified Data.Map as Map
import Data.Traversable (for)
import Data.Void
import Misc.Path hiding (path)
import Module hiding (modulex)
import Simple
import Syntax
import System.Directory
import System.Exit
import System.FilePath
import Text.Megaparsec (SourcePos, errorBundlePretty)
import TypeCheck.Core
import Prelude hiding (readFile, writeFile)
import qualified Prelude

compileFunctionLiteral ::
  [String] ->
  String ->
  TypeSchemeInfer ->
  Term θ KindInfer TypeInfer p ->
  C.Global (C.Representation C.RepresentationFix)
compileFunctionLiteral path name σ e = fmap ctype $ runCodegen (compileFunction sym e' σ') (external e')
  where
    (e', σ') = runReader (convertTermAnnotate e σ) Map.empty
    sym = mangle (Path path name)

compileModule path (CoreModule code) = Map.toList code >>= (uncurry $ compileItem path)

compileItem ::
  [String] ->
  String ->
  Item TypeSchemeInfer θ KindInfer TypeInfer p ->
  [C.Global (C.Representation C.RepresentationFix)]
compileItem path name (Module items) = compileModule (path ++ [name]) items
compileItem path name (Global (Text σ e)) = [compileFunctionLiteral path name σ e]
compileItem _ _ (Global (Inline _ _)) = []
compileItem _ _ (Global (Import _ _)) = []

nameType :: TypeUnify -> Type (KindAuto Internal) Void Internal
nameType (CoreType p (TypeLogical (TypeLogicalRaw i))) = CoreType p $ TypeVariable $ TypeIdentifier $ "_" ++ show i
nameType (CoreType p σ) = CoreType p $ mapTypeF (error "unexpected logic variable") (bimap (mapPattern id (Just . nameKind) id) nameType) (Just . nameKind) nameType σ

nameKind :: KindUnify -> Kind Void Internal
nameKind (CoreKind p (KindLogical (KindLogicalRaw i))) = CoreKind p $ KindVariable $ KindIdentifier $ "_" ++ show i
nameKind (CoreKind p κ) = CoreKind p $ mapKindF (error "unexpected logic variable") nameKind κ

prettyError :: TypeError [SourcePos] -> String
prettyError (UnknownIdentifier p (TermIdentifier x)) = "Unknown identifer " ++ x ++ positions p
prettyError (TypeMismatch p σ σ') = "Type mismatch between ``" ++ pretty typex (nameType σ) ++ "`` and ``" ++ pretty typex (nameType σ') ++ "``" ++ positions p
prettyError (KindMismatch p κ κ') = "Kind mismatch between ``" ++ pretty kind (nameKind κ) ++ "`` and ``" ++ pretty kind (nameKind κ') ++ "``" ++ positions p
prettyError (ConstraintMismatch p c σ) = "Unable to proof ``" ++ pretty constraint c ++ "(" ++ pretty typex (nameType σ) ++ ")``" ++ positions p
prettyError e = show e

newtype PrettyIO a = PrettyIO {runPrettyIO :: IO a} deriving (Functor, Applicative, Monad)

quoted x = "\"" ++ x ++ "\""

prettyIdentifier x = quoted x

prettyPath = quoted . pretty path

expected a b p = "Expected " ++ a ++ " but got " ++ b ++ positions p

prettyModuleError (IllegalPath p path) = "Unknown path " ++ prettyPath path ++ positions p
prettyModuleError (IncompletePath p path) = "Incomplete path " ++ prettyPath path ++ positions p
prettyModuleError (IndexingGlobal p path) = "Indexing global declaration" ++ prettyPath path ++ positions p
prettyModuleError (Cycle p path) = "Global cycle" ++ prettyPath path ++ positions p

positions p = " in positions: " ++ show p

instance ModuleQuit [SourcePos] PrettyIO where
  moduleQuit e = PrettyIO $ die $ prettyModuleError e
  typeQuit e = PrettyIO $ die $ prettyError e

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
  code <- mapModuleAuto (: []) <$> addAll (loadItem command) :: IO (ModuleAuto [SourcePos])
  prettyAll (prettyItem command) (mapModuleAuto (const Internal) code)
  ordering <- runPrettyIO $ order code
  ordering' <- runPrettyIO $ typeCheckModule ordering
  let code' = unorder $ unInfer $ ordering'
  prettyAll (prettyItemAnnotated command) code'
  let ordering'' = reduceModule ordering'
  let code'' = unorder $ unInfer $ ordering''
  prettyAll (prettyItemReduced command) code''
  generateAll (generateCItem command) (unorder $ ordering'')
