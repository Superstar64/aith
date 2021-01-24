module Core.Ast.Stage where

import Core.Ast.Common
import Core.Ast.StagePattern
import qualified Data.Set as Set
import Misc.Identifier
import qualified TypeSystem.Meta as TypeSystem
import TypeSystem.Methods
import qualified TypeSystem.Runtime as TypeSystem
import qualified TypeSystem.Variable as TypeSystem

data StageF p = StageVariable Identifier | Runtime | Meta deriving (Functor, Show)

data Stage p = CoreStage p (StageF p) deriving (Functor, Show)

type StageInternal = Stage Internal

projectStage ::
  StageF p ->
  Either
    (TypeSystem.Variable (Stage p))
    ( Either
        (TypeSystem.Runtime ())
        (TypeSystem.Meta)
    )
projectStage (StageVariable x) = Left $ TypeSystem.Variable x
projectStage Runtime = Right $ Left $ TypeSystem.Runtime ()
projectStage Meta = Right $ Right $ TypeSystem.Meta

instance TypeSystem.EmbedVariable StageInternal where
  variable x = CoreStage Internal $ StageVariable x

instance TypeSystem.EmbedRuntime StageInternal () where
  runtime () = CoreStage Internal $ Runtime

instance TypeSystem.EmbedMeta StageInternal where
  meta = CoreStage Internal $ Meta

instance FreeVariables StageInternal StageInternal where
  freeVariables (CoreStage Internal s) = freeVariables @StageInternal $ projectStage s

instance FreeVariables StageInternal (TypeSystem.Variable StageInternal) where
  freeVariables (TypeSystem.Variable x) = Set.singleton x

instance FreeVariables StageInternal () where
  freeVariables () = Set.empty

instance Substitute StageInternal StageInternal where
  substitute sx x (CoreStage Internal s) = substituteImpl sx x $ projectStage s

instance Substitute StageInternal StagePatternInternal where
  substitute _ _ pm = pm

instance SubstituteImpl (TypeSystem.Variable StageInternal) StageInternal StageInternal where
  substituteImpl sx x (TypeSystem.Variable x') | x == x' = sx
  substituteImpl _ _ (TypeSystem.Variable x) = TypeSystem.variable x

instance Substitute StageInternal () where
  substitute _ _ () = ()

instance ModifyVariables StageInternal StagePatternInternal where
  modifyVariables (CoreStagePattern Internal pm) free = foldr Set.delete free $ bindings (projectStagePattern pm)

instance Reduce StageInternal where
  reduce = id
