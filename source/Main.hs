module Main where

import Ast.Core
import qualified Ast.Surface as Surface
import Ast.Symbol (Path (..), SemiPath (..), TermIdentifier (..))
import qualified Ast.Symbol as Symbol
import qualified C.Print as C
import Codegen
import Control.Monad.Trans.State
import Data.Either (fromRight)
import Data.Foldable
import Data.Functor.Identity
import qualified Data.List as List
import Data.List.NonEmpty (NonEmpty)
import qualified Data.List.NonEmpty as NonEmpty
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (isJust)
import Data.Traversable (for)
import qualified Simple
import Syntax
import System.Console.GetOpt
import System.Directory
import System.Environment
import System.Exit
import System.FilePath
import Text.Megaparsec (SourcePos, errorBundlePretty)
import TypeCheck

unorder = Map.fromListWith (flip (<>)) . map (fmap NonEmpty.singleton)

v = TypeLogical (TypeLogicalRaw 0)

prettyType σ = pretty Syntax.typex (nameType σ)

prettyError :: TypeError [SourcePos] -> String
prettyError e = case e of
  TypeMismatch p σ σ' ->
    "Type mismatch between `" ++ prettyType σ ++ "` and `" ++ prettyType σ' ++ "`" ++ positions p
  ErasureMismatch p π π' ->
    "Erasure mismatch between `" ++ show π ++ "` and `" ++ show π' ++ "`" ++ positions p
  TypePolyMismatch p ς ς' ->
    prettyError
      (TypeMismatch p (TypeScheme AmbiguousLabel ς) (TypeScheme AmbiguousLabel ς'))
  TypeBooleanMismatch p σ -> "Unable to solve boolean expressions: " ++ List.intercalate " and " (map prettyType σ) ++ positions p
  ExpectedTypeAnnotation p -> "Expected type annotation: " ++ positions p
  ExpectedBooleanType p σ -> "Expected boolean type: " ++ prettyType σ ++ positions p
  AmbiguousType p σ -> "Ambiguous Type: `" ++ pretty Syntax.typex (nameType $ flexible σ) ++ "`" ++ positions p
  UnknownGlobalIdentifier p x -> "Unknown Global: " ++ pretty termGlobalIdentifier x ++ positions p
  UnknownTypeGlobalIdentifier p x -> "Unknown Type Global: " ++ pretty typeGlobalIdentifier x ++ positions p
  TypeOccursCheck p v σ ->
    "Occurance Check: `" ++ prettyType (TypeLogical v) ++ "` in` " ++ prettyType σ ++ "`" ++ positions p
  EscapingSkolemType p x ->
    "Escaping Skolem: `" ++ pretty typeIdentifier x ++ "`" ++ positions p
  MismatchedTypeLambdas p -> "Mismatched type lambdas: " ++ positions p
  IncorrectRegionBounds p -> "Incorrect Region Bounds: " ++ positions p
  NotTypable p -> "Not typable: " ++ positions p
  ExpectedNewtype p σ -> "Expected Newtype: `" ++ prettyType σ ++ "`" ++ positions p
  ExpectedKind p σ -> prettyError (TypeMismatch p (Kind v) σ)
  ExpectedRepresentation p σ -> prettyError (TypeMismatch p (Kind v) σ)
  ExpectedMultiplicity p σ -> prettyError (TypeMismatch p (Kind v) σ)
  ExpectedSize p σ -> prettyError (TypeMismatch p (Size) σ)
  ExpectedSignedness p σ -> prettyError (TypeMismatch p (Signedness) σ)
  ExpectedType p σ -> prettyError (TypeMismatch p (Type) σ)
  ExpectedPretype p σ -> prettyError (TypeMismatch p (Pretype v v) σ)
  ExpectedBoxed p σ -> prettyError (TypeMismatch p (Boxed) σ)
  ExpectedRegion p σ -> prettyError (TypeMismatch p (Region) σ)
  ExpectedPropositional p σ -> prettyError (TypeMismatch p (Propositional) σ)
  ExpectedUnification p σ -> prettyError (TypeMismatch p (Unification) σ)
  ExpectedInline p σ -> prettyError (TypeMismatch p (Inline v v v) σ)
  ExpectedFunctionPointer p n σ -> prettyError (TypeMismatch p (FunctionPointer (replicate n v) v v) σ)
  ExpectedFunctionLiteralType p n σ -> prettyError (TypeMismatch p (FunctionLiteralType (replicate n v) v v) σ)
  ExpectedUnique p σ -> prettyError (TypeMismatch p (Unique v) σ)
  ExpectedPointer p σ -> prettyError (TypeMismatch p (Pointer v) σ)
  ExpectedArray p σ -> prettyError (TypeMismatch p (Array v) σ)
  ExpectedEffect p σ -> prettyError (TypeMismatch p (Effect v v) σ)
  ExpectedShared p σ -> prettyError (TypeMismatch p (Shared v v) σ)
  ExpectedNumber p σ -> prettyError (TypeMismatch p (Number v v) σ)
  ExpectedBoolean p σ -> prettyError (TypeMismatch p (Boolean) σ)
  ExpectedStep p σ -> prettyError (TypeMismatch p (Step v v) σ)
  ExpectedLabel p σ -> prettyError (TypeMismatch p (Label) σ)
  BadBorrowIdentifier p (TermIdentifier x) -> "Bad Borrow Identifier `" ++ x ++ "`" ++ positions p
  BadBorrowSyntax p -> "Bad Borrow Syntax" ++ positions p
  InstantiationLengthMismatch p -> "Mismatch Instanciation Length" ++ positions p
  NotErasable p σ -> "Representation not erasable: `" ++ prettyType σ ++ "`" ++ positions p

quoted x = "\"" ++ x ++ "\""

prettyIdentifier x = quoted x

prettyPath = quoted . pretty path

expected a b p = "Expected " ++ a ++ " but got " ++ b ++ positions p

prettyModuleError (Surface.IllegalPath p path) = "Unknown path " ++ prettyPath path ++ positions p
prettyModuleError (Surface.Cycle p path) = "Global variable cycle " ++ prettyPath path ++ positions p
prettyModuleError (Surface.Duplicate p path) = "Duplicate declarations " ++ prettyPath path ++ positions p

positions p = " in positions: " ++ show p

data CommandLine = CommandLine
  { loadItem :: [(SemiPath, FilePath)],
    prettyItem :: [(SemiPath, FilePath)],
    prettyItemAnnotated :: [(SemiPath, FilePath)],
    prettyItemReduced :: [(SemiPath, FilePath)],
    generateCItem :: [(SemiPath, FilePath)]
  }
  deriving (Show)

baseMain command = do
  code <- foldrM (\item code -> Map.union <$> loadSection item <*> pure code) Map.empty (loadItem command)
  code <- handleModuleError $ Surface.order code
  let (origin, paths, items) = unzip3 code
  for (prettyItem command) (saveSection $ unorder $ Surface.removeInserted (zip3 origin paths items))
  (code, environment) <- handleTypeError $ runStateT (typeCheckModule (zip paths items)) emptyEnvironment
  let (paths, items) = unzip code
  for (prettyItemAnnotated command) (saveSection $ unorder $ fmap global <$> Surface.removeInserted (zip3 origin paths items))

  code <- pure $ reduceModule code
  let (paths, items) = unzip code

  for (prettyItemReduced command) (saveSection $ unorder $ fmap global <$> Surface.removeInserted (zip3 origin paths items))
  for (generateCItem command) (saveC environment code)
  pure ()
  where
    readFile "-" = getContents
    readFile name = do
      file <- Prelude.readFile name
      pure $ length file `seq` file -- stop lazy io
    writeFile "-" file = putStrLn file
    writeFile name file = Prelude.writeFile name file

    handleModuleError (Left e) = die $ prettyModuleError e
    handleModuleError (Right e) = pure e
    handleTypeError (Left e) = die $ prettyError e
    handleTypeError (Right e) = pure e
    loadSection :: (SemiPath, FilePath) -> IO (Map Path (NonEmpty (Surface.Global [SourcePos])))
    loadSection (semi, fileName) = do
      directory <- doesDirectoryExist fileName
      case directory of
        False -> do
          file <- readFile fileName
          case parseMain items fileName file of
            Right items -> pure (Map.mapKeysMonotonic (Symbol.prepend semi) (Map.map (fmap (fmap (: []))) items))
            Left err -> die $ errorBundlePretty err
        True -> do
          fileNames <- listDirectory fileName
          modules <- traverse (\name -> loadSection (Symbol.forget $ Symbol.combine semi (dropExtension name), fileName </> name)) fileNames
          pure $ Map.unions modules

    saveSection :: Map Path (NonEmpty (Surface.Global p)) -> (SemiPath, FilePath) -> IO ()
    saveSection code (semi, fileName) = do
      code <- pure $ (Surface.removeInserted $ fromRight undefined $ Surface.order ((fmap . fmap . fmap) (const ()) code)) >>= starts
      let text = pretty itemsRaw code
      writeFile fileName text
      where
        starts (path, item) = do
          case Symbol.startsWith semi path of
            Nothing -> []
            Just path -> [(path, item)]

    saveC environment code (semi, fileName) = do
      writeFile fileName $ C.emit C.code (dependency ++ statements)
      where
        (statements, dependency) = runDependency $ do
          let wrappers = fmap (assumeDone . typeKind) (kindGlobalEnvironment environment)
          code <- pure $ filter (isJust . Symbol.startsWith semi . fst) code
          fmap concat $
            for code $ \(path, item) -> case item of
              Text e -> do
                let context = Simple.Context {Simple.localKinds = Map.empty, Simple.globalKinds = wrappers}
                    σ = textType e
                    e' = Simple.convertFunction context e
                    σ' = Simple.convertFunctionType context σ
                (: []) <$> codegen (Symbol.mangle path) σ' e'
              _ -> pure []
          where
            assumeDone = runIdentity . zonkType (error "bad unification vaniable")

data Flags
  = Help
  | Load String
  | Output String
  | Directory String
  | Format
  | Annotate
  | Reduce
  | C
  deriving (Show, Eq)

main' args = do
  let (flags, _, errors) = getOpt (ReturnInOrder Load) descriptions args
  if
      | (_ : _) <- errors -> die $ List.intercalate "\n" errors
      | [] <- flags -> printHelp
      | Just _ <- find (== Help) flags -> printHelp
      | otherwise -> do
          let options = targets flags
          cmd <- foldlM processCmd (CommandLine [] [] [] [] []) options
          baseMain cmd
  where
    descriptions =
      [ Option [] ["help"] (NoArg Help) "Help",
        Option ['d'] ["directory"] (ReqArg Directory "path") "Set",
        Option ['o'] ["output"] (ReqArg Output "file") "Output",
        Option ['F'] ["format"] (NoArg Format) "Format",
        Option ['A'] ["annotate"] (NoArg Annotate) "Annotate",
        Option ['R'] ["reduce"] (NoArg Reduce) "Reduce",
        Option ['C'] [] (NoArg C) "C"
      ]

    printHelp = do
      traverse
        putStrLn
        [ "Usage: aith [options] file...",
          "Options:",
          " -o<file>",
          "     Set output file",
          " -d<aith path>",
          " --directory <aith path>",
          "     Set the Aith path for the next command",
          " -F",
          " --format",
          "     Format the output",
          " -A",
          " --annotate",
          "     Annotate the outpt",
          " -R",
          " --reduce",
          "     Reduce the output",
          " -C",
          "     Generate C into the output"
        ]
      exitSuccess
    targets [] = [[]]
    targets (x@(Load _) : xs) = [x] : targets xs
    targets (x@(Output _) : xs) = [x] : targets xs
    targets (x : xs) = (x : head remain) : tail remain
      where
        remain = targets xs

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

        findLoad [] = []
        findLoad (Load load : xs) = load : findLoad xs
        findLoad (_ : xs) = findLoad xs

        findOutput [] = []
        findOutput (Output output : xs) = output : findOutput xs
        findOutput (_ : xs) = findOutput xs

        findWorking [] = []
        findWorking (Directory wd : xs) = wd : findWorking xs
        findWorking (_ : xs) = findWorking xs

        countFormat = length . filter (== Format)

        countAnnotate = length . filter (== Annotate)

        countReduce = length . filter (== Reduce)

        countC = length . filter (== C)

        loadCmd item command = command {loadItem = item : loadItem command}

        formatCmd item command = command {prettyItem = item : prettyItem command}

        annotateCmd item command = command {prettyItemAnnotated = item : prettyItemAnnotated command}

        reduceCmd item command = command {prettyItemReduced = item : prettyItemReduced command}

        cCmd item command = command {generateCItem = item : generateCItem command}
        parsePathPair modify filePath targetPath cmd = case parseMaybe semiPath targetPath of
          Nothing -> die $ "Unable to parse path: " ++ targetPath
          Just path -> pure $ modify (path, filePath) cmd

main = getArgs >>= main'
