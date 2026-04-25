import Gnosis.FailureComposition

namespace Gnosis

structure SparseBranchSnapshot where
  branchId : Nat
  survives : Bool
  output : List Nat
deriving DecidableEq, Repr

def sparseStageSupport (stage : List SparseBranchSnapshot) : List Nat :=
  stage.map SparseBranchSnapshot.branchId

def sparseStagesSupport : List (List SparseBranchSnapshot) -> List Nat
  | [] => []
  | stage :: rest => sparseStageSupport stage ++ sparseStagesSupport rest

def sparseSystemSupport
    (start : List SparseBranchSnapshot)
    (stages : List (List SparseBranchSnapshot)) : List Nat :=
  ((sparseStageSupport start) ++ sparseStagesSupport stages).eraseDups

structure ChoiceSystem where
  initial : List SparseBranchSnapshot
  recovery : List (List SparseBranchSnapshot)
deriving Repr

def ChoiceSystem.support (system : ChoiceSystem) : List Nat :=
  sparseSystemSupport system.initial system.recovery

structure ChoiceTrajectory where
  initial : List SparseBranchSnapshot
  recovery : Nat -> List SparseBranchSnapshot

def ChoiceTrajectory.prefixStages
    (trajectory : ChoiceTrajectory)
    (depth : Nat) : List (List SparseBranchSnapshot) :=
  List.ofFn (fun index : Fin depth => trajectory.recovery index.1)

def ChoiceTrajectory.prefixSystem
    (trajectory : ChoiceTrajectory)
    (depth : Nat) : ChoiceSystem :=
  { initial := trajectory.initial, recovery := trajectory.prefixStages depth }

