import Init
import Gnosis.BuleyeanProbability
import Gnosis.GoodhartsLaw

namespace Gnosis
namespace NonEmpiricalPrediction

/-!
# Non-Empirical Prediction: structural hole as void boundary

Matches `open-source/gnosis/tla/NonEmpiricalPrediction.tla` invariants and Formal
Theorem Ledger rows §15.22 (e.g. `THM-MENDELEEV-is-COMPLEMENT`,
`THM-LATTICE-PARTITION`, `THM-REJECTION-REDUCES-PREDICTION`).

The complement interpolation coincides with `BuleyeanSpace.weight` when rounds
and per-choice void data align — see `mendeleev_is_complement`.
-/

/-- Neighbor-aggregated structural hole: void sum and observation rounds (TLA names). -/
structure StructuralHole where
  neighborVoidSum : Nat
  neighborRoundsSum : Nat
  hVoidLe : neighborVoidSum ≤ neighborRoundsSum
  hRoundsPos : 0 < neighborRoundsSum

/-- Mendeleev / Buleyean complement interpolation: `R - min(v,R) + 1`. -/
def StructuralHole.interpolationWeight (h : StructuralHole) : Nat :=
  h.neighborRoundsSum - Nat.min h.neighborVoidSum h.neighborRoundsSum + 1

def StructuralHole.uninformedWeight (h : StructuralHole) : Nat :=
  h.neighborRoundsSum + 1

/-- InvPositiveWeight + bound from TLA. -/
theorem hole_has_positive_weight (h : StructuralHole) : 0 < h.interpolationWeight := by
  unfold StructuralHole.interpolationWeight
  exact Nat.succ_pos _

theorem interpolation_weight_one_le (h : StructuralHole) : 1 ≤ h.interpolationWeight := by
  exact Nat.succ_le_of_lt (hole_has_positive_weight h)

theorem interpolation_weight_bounded (h : StructuralHole) :
    h.interpolationWeight ≤ h.neighborRoundsSum + 1 := by
  unfold StructuralHole.interpolationWeight
  refine Nat.add_le_add_right (Nat.sub_le h.neighborRoundsSum _) 1

theorem uninformed_eq_rounds_succ (h : StructuralHole) :
    h.uninformedWeight = h.neighborRoundsSum + 1 := rfl

/-- InvStructureDominates: interpolation never exceeds uninformed guessing mass. -/
theorem neighbor_dominates_uninformed (h : StructuralHole) :
    h.interpolationWeight ≤ h.uninformedWeight := by
  unfold StructuralHole.interpolationWeight StructuralHole.uninformedWeight
  exact Nat.add_le_add_right (Nat.sub_le h.neighborRoundsSum _) 1

/-- Strict gap when neighbors report rejection (`THM-STRICT-DOMINANCE` specialisation). -/
theorem strict_dominance_with_rejection (h : StructuralHole)
    (hv : 0 < h.neighborVoidSum) :
    h.interpolationWeight < h.uninformedWeight := by
  simp [StructuralHole.interpolationWeight, StructuralHole.uninformedWeight, Nat.min_eq_left h.hVoidLe]
  exact Nat.sub_lt_self hv h.hVoidLe

/-- Same rounds, more void ⇒ lower interpolation weight (via `goodhart_strict_antitone`). -/
theorem rejection_reduces_prediction
    (h₁ h₂ : StructuralHole)
    (hRsum : h₁.neighborRoundsSum = h₂.neighborRoundsSum)
    (hV : h₁.neighborVoidSum < h₂.neighborVoidSum) :
    h₂.interpolationWeight < h₁.interpolationWeight := by
  have hhi : h₂.neighborVoidSum ≤ h₁.neighborRoundsSum :=
    Nat.le_trans h₂.hVoidLe (Nat.le_of_eq hRsum.symm)
  have hg :=
    goodhart_strict_antitone h₁.neighborRoundsSum h₁.neighborVoidSum h₂.neighborVoidSum
      h₁.hVoidLe hhi hV
  have e1 :
      godWeight h₁.neighborRoundsSum h₁.neighborVoidSum = h₁.interpolationWeight := by
    unfold godWeight StructuralHole.interpolationWeight
    simp [Nat.min_eq_left h₁.hVoidLe]
  have e2 :
      godWeight h₁.neighborRoundsSum h₂.neighborVoidSum = h₂.interpolationWeight := by
    unfold godWeight StructuralHole.interpolationWeight
    simp [hRsum, Nat.min_eq_left h₂.hVoidLe]
  rw [e1, e2] at hg
  exact (gt_iff_lt.mp hg)

/-- Different void data ⇒ different predictions (`THM-HOLES-ORDERED`). -/
theorem holes_ordered
    (h₁ h₂ : StructuralHole)
    (hR : h₁.neighborRoundsSum = h₂.neighborRoundsSum)
    (hV : h₁.neighborVoidSum ≠ h₂.neighborVoidSum) :
    h₁.interpolationWeight ≠ h₂.interpolationWeight := by
  intro heq
  rcases Nat.lt_trichotomy h₁.neighborVoidSum h₂.neighborVoidSum with hlt | he | hgt
  · have hw := rejection_reduces_prediction h₁ h₂ hR hlt
    rw [heq] at hw
    exact Nat.lt_irrefl _ hw
  · rw [he] at hV
    exact absurd rfl hV
  · have hw := rejection_reduces_prediction h₂ h₁ hR.symm hgt
    rw [← heq] at hw
    exact Nat.lt_irrefl _ hw

/-- Lattice with a concrete partition witness (`THM-LATTICE-PARTITION`). -/
structure StructuralLattice where
  latticeSize : Nat
  observedCount : Nat
  holeCount : Nat
  hPartition : observedCount + holeCount = latticeSize

theorem lattice_partition (L : StructuralLattice) :
    L.observedCount + L.holeCount = L.latticeSize :=
  L.hPartition

/-- At least one hole exists (for algebraic-hole narrative). -/
structure StructuralLatticeWithHole extends StructuralLattice where
  hHoleOne : 0 < holeCount

theorem algebraic_hole_positive (L : StructuralLatticeWithHole) : 0 < L.holeCount :=
  L.hHoleOne

/-- Ledger isomorphism: hole interpolation equals Buleyean complement weight on aligned data. -/
theorem mendeleev_is_complement
    (h : StructuralHole)
    (bs : BuleyeanSpace)
    (i : Fin bs.numChoices)
    (hR : bs.rounds = h.neighborRoundsSum)
    (hV : bs.voidBoundary i = h.neighborVoidSum) :
    h.interpolationWeight = bs.weight i := by
  unfold StructuralHole.interpolationWeight BuleyeanSpace.weight
  simp [hR, hV]

/-- Positive weight for an unobserved slot — formal “impossible element” hook (`THM-IMPOSSIBLE-ELEMENT`). -/
theorem impossible_element (h : StructuralHole) : 0 < h.interpolationWeight :=
  hole_has_positive_weight h

/-- Prediction mass from void boundary alone (`THM-PREDICTION-WITHOUT-OBSERVATION`). -/
theorem prediction_without_observation (h : StructuralHole) : 0 < h.interpolationWeight :=
  hole_has_positive_weight h

/-- Master bundle: partition, positivity, boundedness, dominance (`THM-NON-EMPIRICAL-PREDICTION-MASTER`). -/
theorem non_empirical_prediction_master (h : StructuralHole) (L : StructuralLattice) :
    (0 < h.interpolationWeight) ∧
    (h.interpolationWeight ≤ h.neighborRoundsSum + 1) ∧
    (h.interpolationWeight ≤ h.uninformedWeight) ∧
    (L.observedCount + L.holeCount = L.latticeSize) :=
  ⟨hole_has_positive_weight h, interpolation_weight_bounded h, neighbor_dominates_uninformed h,
    lattice_partition L⟩

end NonEmpiricalPrediction
end Gnosis
