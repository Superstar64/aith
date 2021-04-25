module C.Ast where

import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.State (evalStateT, get, modify)
import Control.Monad.Trans.Writer (runWriter, tell)
import qualified Data.Set as Set
import Misc.Prism

data Representation x = Pointer | Struct x deriving (Show, Eq, Ord)

pointer = Prism (const Pointer) $ \case
  Pointer -> Just ()
  _ -> Nothing

struct = Prism Struct $ \case
  (Struct x) -> Just x
  _ -> Nothing

data RepresentationFix = RepresentationFix ([Representation RepresentationFix]) deriving (Show, Eq, Ord)

mangleType Pointer = "p"
mangleType (Struct (RepresentationFix items)) = "s" ++ (items >>= mangleType) ++ "e"

fields = map (\x -> '_' : show x) [0 ..]

escapeStruct Pointer = pure Pointer
escapeStruct (Struct (RepresentationFix items)) = do
  let mangling = "s" ++ (items >>= mangleType) ++ "e"
  solved <- get
  if items `Set.notMember` solved
    then do
      modify $ Set.insert items
      items' <- traverse escapeStruct items
      lift $ tell [StructDefinition mangling (zip items' fields)]
    else pure ()
  pure $ Struct $ mangling

escapeStructs :: [Global (Representation RepresentationFix)] -> ([Global (Representation String)], [Global (Representation String)])
escapeStructs x = runWriter $ evalStateT (traverse (traverse escapeStruct) x) (Set.empty)

data Global x
  = FunctionDefinition x String [(x, String)] [Statement x]
  | StructDefinition String [(x, String)]
  deriving (Show, Functor, Foldable, Traversable)

functionDefinition = Prism (uncurry $ uncurry $ uncurry $ FunctionDefinition) $ \case
  (FunctionDefinition returnType name arguments text) -> Just (((returnType, name), arguments), text)
  _ -> Nothing

structDefinition = Prism (uncurry StructDefinition) $ \case
  (StructDefinition name items) -> Just (name, items)
  _ -> Nothing

data Statement x
  = Return (Expression x)
  | ForwardDeclare x String [x]
  | VariableDeclaration x String (Expression x)
  deriving (Show, Functor, Foldable, Traversable)

returnx = Prism Return $ \case
  (Return e) -> Just e
  _ -> Nothing

forwardDeclare = Prism (uncurry $ uncurry $ ForwardDeclare) $ \case
  (ForwardDeclare returnType name argumentTypes) -> Just ((returnType, name), argumentTypes)
  _ -> Nothing

variableDeclation = Prism (uncurry $ uncurry $ VariableDeclaration) $ \case
  (VariableDeclaration variableType name value) -> Just ((variableType, name), value)
  _ -> Nothing

data Expression x
  = Variable String
  | Call x [x] (Expression x) [Expression x]
  | CompoundLiteral x [Expression x]
  | Member (Expression x) String
  deriving (Show, Functor, Foldable, Traversable)

variable = Prism Variable $ \case
  (Variable x) -> Just x
  _ -> Nothing

call = Prism (uncurry $ uncurry $ uncurry $ Call) $ \case
  (Call returnType argumentTypes function arguments) -> Just (((returnType, argumentTypes), function), arguments)
  _ -> Nothing

compoundLiteral = Prism (uncurry $ CompoundLiteral) $ \case
  (CompoundLiteral typex items) -> Just (typex, items)
  _ -> Nothing

member = Prism (uncurry $ Member) $ \case
  (Member value name) -> Just (value, name)
  _ -> Nothing
