import Init
import Gnosis.GoodhartsLaw
import Gnosis.NonEmpiricalPrediction

namespace Gnosis

/-!
# SolomonoffSpace (thin layer)

Discrete “description budget” `R` and Kolmogorov-style complexity `K ≤ R`.
Prior mass uses the same complement line as `godWeight` / `StructuralHole`.

`THM-NON-EMPIRICAL-SOLOMONOFF`: when void mass and rounds on a structural hole
line up with `(complexity, budget)`, the non-empirical interpolation coincides
with this prior (`non_empirical_solomonoff_compose`).
-/

structure SolomonoffSpace where
  /-- Observation / enumeration budget (matches neighbor rounds on the hole line). -/
  budget : Nat
  /-- Kolmogorov-style description length, bounded by the budget. -/
  complexity : Nat
  hBudgetPos : 0 < budget
  hKLe : complexity ≤ budget

def SolomonoffSpace.priorWeight (s : SolomonoffSpace) : Nat :=
  godWeight s.budget s.complexity

theorem priorWeight_eq_god (s : SolomonoffSpace) :
    s.priorWeight = godWeight s.budget s.complexity :=
  rfl

/-- Simpler hypothesis (lower `complexity`) ⇒ higher prior mass at fixed budget. -/
theorem solomonoff_complexity_antitone
    (s₁ s₂ : SolomonoffSpace)
    (hB : s₁.budget = s₂.budget)
    (hLT : s₁.complexity < s₂.complexity) :
    s₂.priorWeight < s₁.priorWeight := by
  have hhi : s₂.complexity ≤ s₁.budget := hB.symm ▸ s₂.hKLe
  have hg :=
    goodhart_strict_antitone s₁.budget s₁.complexity s₂.complexity s₁.hKLe hhi hLT
  have hL : godWeight s₂.budget s₂.complexity = godWeight s₁.budget s₂.complexity := by rw [hB]
  rw [SolomonoffSpace.priorWeight, SolomonoffSpace.priorWeight, hL]
  exact gt_iff_lt.mp hg

namespace NonEmpiricalPrediction

theorem non_empirical_solomonoff_compose
    (h : StructuralHole)
    (s : SolomonoffSpace)
    (hR : h.neighborRoundsSum = s.budget)
    (hK : h.neighborVoidSum = s.complexity) :
    h.interpolationWeight = s.priorWeight := by
  have eh :
      h.interpolationWeight = godWeight h.neighborRoundsSum h.neighborVoidSum := by
    unfold StructuralHole.interpolationWeight godWeight
    simp [Nat.min_eq_left h.hVoidLe]
  rw [eh, hR, hK]
  rfl

end NonEmpiricalPrediction

end Gnosis
