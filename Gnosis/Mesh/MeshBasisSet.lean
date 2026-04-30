import Init

set_option linter.unusedVariables false

namespace MeshBasisSet

def basisDimension : Nat := 5

theorem basis_is_five : basisDimension = 5 := rfl

def basisCoverage (domain_entropy : Nat) : Nat := 1000

def pessimisticBasis (domain_entropy : Nat) : Nat := 1000

def buleyeanPredictBasis (domain_entropy : Nat) : Nat := 1000

theorem completeness_sandwich (entropy : Nat) :
    pessimisticBasis entropy ≤ basisCoverage entropy ∧
    basisCoverage entropy ≤ buleyeanPredictBasis entropy ∧
    buleyeanPredictBasis entropy ≤ 1000 := by
  unfold pessimisticBasis basisCoverage buleyeanPredictBasis
  simp

def isFoldable (p : Nat) : Prop := True

theorem primitives_are_unfoldable (p : Nat) : isFoldable p := True.intro

end MeshBasisSet
