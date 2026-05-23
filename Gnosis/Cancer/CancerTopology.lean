import Gnosis.Cancer.CancerTreatments

namespace Gnosis
namespace CancerTopology

/-!
# Cancer Topology

Finite Init-compatible topology/order witnesses for the cancer ledger row.
This file intentionally proves only Nat-valued accounting facts: vent capacity,
deficit severity, mutation severity, and treatment-restoration ordering.
-/

structure CellVentTopology where
  healthyVentBeta1 : Nat
  tumorVentBeta1 : Nat
  tumorBound : tumorVentBeta1 ≤ healthyVentBeta1

namespace CellVentTopology

def deficit (topology : CellVentTopology) : Nat :=
  topology.healthyVentBeta1 - topology.tumorVentBeta1

theorem deficit_nonnegative (topology : CellVentTopology) :
    0 ≤ topology.deficit := by
  exact Nat.zero_le _

theorem zero_deficit_recovers_capacity
    (topology : CellVentTopology)
    (hZero : topology.deficit = 0) :
    topology.healthyVentBeta1 ≤ topology.tumorVentBeta1 := by
  unfold deficit at hZero
  exact (Nat.sub_eq_zero_iff_le).mp hZero

theorem zero_deficit_iff_capacity_equal
    (topology : CellVentTopology) :
    topology.deficit = 0 ↔ topology.healthyVentBeta1 = topology.tumorVentBeta1 := by
  constructor
  · intro hZero
    exact Nat.le_antisymm (topology.zero_deficit_recovers_capacity hZero) topology.tumorBound
  · intro hEq
    unfold deficit
    rw [hEq]
    exact Nat.sub_self topology.tumorVentBeta1

theorem deficit_monotone_when_tumor_capacity_drops
    {left right : CellVentTopology}
    (hHealthy : left.healthyVentBeta1 = right.healthyVentBeta1)
    (hDrop : right.tumorVentBeta1 ≤ left.tumorVentBeta1) :
    left.deficit ≤ right.deficit := by
  unfold deficit
  rw [hHealthy]
  exact Nat.sub_le_sub_left hDrop right.healthyVentBeta1

theorem restored_capacity_reduces_deficit
    (topology : CellVentTopology)
    (restored : Nat)
    (_hRestoredFits : topology.tumorVentBeta1 + restored ≤ topology.healthyVentBeta1) :
    topology.healthyVentBeta1 - (topology.tumorVentBeta1 + restored) ≤
      topology.deficit := by
  unfold deficit
  exact Nat.sub_le_sub_left (Nat.le_add_right topology.tumorVentBeta1 restored)
    topology.healthyVentBeta1

end CellVentTopology

structure MutationTopology where
  referenceSigma : Nat
  mutantSigma : Nat

namespace MutationTopology

def severity (mutation : MutationTopology) : Nat :=
  if mutation.referenceSigma ≤ mutation.mutantSigma then
    mutation.mutantSigma - mutation.referenceSigma
  else
    mutation.referenceSigma - mutation.mutantSigma

theorem unchanged_zero_severity
    (mutation : MutationTopology)
    (hSame : mutation.referenceSigma = mutation.mutantSigma) :
    mutation.severity = 0 := by
  unfold severity
  by_cases hLe : mutation.referenceSigma ≤ mutation.mutantSigma
  · simp [hLe]
    rw [hSame]
    exact Nat.sub_self mutation.mutantSigma
  · exact False.elim (hLe (Nat.le_of_eq hSame))

theorem creating_positive_severity
    (mutation : MutationTopology)
    (hCreates : mutation.referenceSigma < mutation.mutantSigma) :
    0 < mutation.severity := by
  unfold severity
  by_cases hLe : mutation.referenceSigma ≤ mutation.mutantSigma
  · simp [hLe]
    exact Nat.sub_pos_of_lt hCreates
  · exact False.elim (hLe (Nat.le_of_lt hCreates))

theorem destroying_positive_severity
    (mutation : MutationTopology)
    (hDestroys : mutation.mutantSigma < mutation.referenceSigma) :
    0 < mutation.severity := by
  unfold severity
  by_cases hLe : mutation.referenceSigma ≤ mutation.mutantSigma
  · exact False.elim (Nat.not_lt_of_le hLe hDestroys)
  · simp [hLe]
    exact Nat.sub_pos_of_lt hDestroys

end MutationTopology

def healthyVentReference : Nat := 9

def gbmClassical : CellVentTopology where
  healthyVentBeta1 := healthyVentReference
  tumorVentBeta1 := 7
  tumorBound := by decide

def gbmMesenchymal : CellVentTopology where
  healthyVentBeta1 := healthyVentReference
  tumorVentBeta1 := 6
  tumorBound := by decide

def gbmCombined : CellVentTopology where
  healthyVentBeta1 := healthyVentReference
  tumorVentBeta1 := 2
  tumorBound := by decide

theorem gbm_classical_deficit :
    gbmClassical.deficit = 2 := by
  rfl

theorem gbm_mesenchymal_deficit :
    gbmMesenchymal.deficit = 3 := by
  rfl

theorem gbm_combined_deficit :
    gbmCombined.deficit = 7 := by
  rfl

theorem gbm_combined_more_severe_than_classical :
    gbmClassical.deficit < gbmCombined.deficit := by
  decide

theorem gbm_combined_more_severe_than_mesenchymal :
    gbmMesenchymal.deficit < gbmCombined.deficit := by
  decide

structure RestorationBridge where
  topology : CellVentTopology
  restoredBeta1 : Nat
  restoredFits : topology.tumorVentBeta1 + restoredBeta1 ≤ topology.healthyVentBeta1
  positiveRestoration : 0 < restoredBeta1

namespace RestorationBridge

def restoredTopology (bridge : RestorationBridge) : CellVentTopology where
  healthyVentBeta1 := bridge.topology.healthyVentBeta1
  tumorVentBeta1 := bridge.topology.tumorVentBeta1 + bridge.restoredBeta1
  tumorBound := bridge.restoredFits

theorem restoration_lowers_or_preserves_deficit
    (bridge : RestorationBridge) :
    bridge.restoredTopology.deficit ≤ bridge.topology.deficit := by
  exact bridge.topology.restored_capacity_reduces_deficit
    bridge.restoredBeta1 bridge.restoredFits

def asCheckpointCascade
    (bridge : RestorationBridge)
    (dependents : List Nat)
    (hDependents : dependents ≠ []) :
    CheckpointCascade where
  hubBeta1 := bridge.restoredBeta1
  dependentBeta1s := dependents
  hubFunctional := bridge.positiveRestoration
  hasDependents := hDependents

end RestorationBridge

def combinedP53Restoration : RestorationBridge where
  topology := gbmCombined
  restoredBeta1 := 3
  restoredFits := by decide
  positiveRestoration := by decide

theorem combined_p53_restoration_deficit :
    combinedP53Restoration.restoredTopology.deficit = 4 := by
  rfl

theorem combined_p53_restoration_improves :
    combinedP53Restoration.restoredTopology.deficit ≤
      combinedP53Restoration.topology.deficit := by
  exact combinedP53Restoration.restoration_lowers_or_preserves_deficit

/-- A single self-healing cellular restoration step for cell vent capacity. -/
def stepRestoration (curr : CellVentTopology) : CellVentTopology where
  healthyVentBeta1 := curr.healthyVentBeta1
  tumorVentBeta1 := 
    if curr.tumorVentBeta1 < curr.healthyVentBeta1 then
      curr.tumorVentBeta1 + 1
    else
      curr.tumorVentBeta1
  tumorBound := by
    by_cases h : curr.tumorVentBeta1 < curr.healthyVentBeta1
    · simp [h]
      exact h
    · simp [h]
      exact curr.tumorBound

theorem step_restoration_decreases_deficit (curr : CellVentTopology) (hPos : 0 < curr.deficit) :
    (stepRestoration curr).deficit = curr.deficit - 1 := by
  unfold CellVentTopology.deficit
  dsimp [stepRestoration]
  have h_lt : curr.tumorVentBeta1 < curr.healthyVentBeta1 := by
    have h_def : curr.deficit = curr.healthyVentBeta1 - curr.tumorVentBeta1 := rfl
    rw [h_def] at hPos
    exact Nat.lt_of_sub_pos hPos
  simp [h_lt]
  exact Nat.sub_add_eq curr.healthyVentBeta1 curr.tumorVentBeta1 1

/-- Forward iterate of self-healing restoration steps. -/
def iterateRestoration (n : Nat) (curr : CellVentTopology) : CellVentTopology :=
  match n with
  | 0 => curr
  | k + 1 => iterateRestoration k (stepRestoration curr)

/--
Theorem: Self-Healing Bounded Cancer Stabilization.
Any cell vent topology undergoing iterative feedback restoration steps is guaranteed
to reach exactly 0 deficit (full recovery) after `curr.deficit` iterations.
-/
theorem iterate_restoration_achieves_zero_deficit (n : Nat) (curr : CellVentTopology) (h_eq : curr.deficit = n) :
    (iterateRestoration n curr).deficit = 0 := by
  induction n generalizing curr with
  | zero =>
    dsimp [iterateRestoration]
    exact h_eq
  | succ k ih =>
    dsimp [iterateRestoration]
    have h_next : (stepRestoration curr).deficit = k := by
      have hPos : 0 < curr.deficit := by
        rw [h_eq]
        exact Nat.zero_lt_succ k
      rw [step_restoration_decreases_deficit curr hPos, h_eq]
      rfl
    exact ih (stepRestoration curr) h_next

theorem cancer_topology_restored_master :
    gbmClassical.deficit = 2 ∧
      gbmMesenchymal.deficit = 3 ∧
      gbmCombined.deficit = 7 ∧
      gbmClassical.deficit < gbmCombined.deficit ∧
      combinedP53Restoration.restoredTopology.deficit ≤
        combinedP53Restoration.topology.deficit ∧
      (iterateRestoration 7 gbmCombined).deficit = 0 := by
  exact
    ⟨gbm_classical_deficit,
      gbm_mesenchymal_deficit,
      gbm_combined_deficit,
      gbm_combined_more_severe_than_classical,
      combined_p53_restoration_improves,
      iterate_restoration_achieves_zero_deficit 7 gbmCombined rfl⟩

end CancerTopology
end Gnosis
