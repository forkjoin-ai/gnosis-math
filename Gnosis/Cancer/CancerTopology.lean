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

theorem cancer_topology_restored_master :
    gbmClassical.deficit = 2 ∧
      gbmMesenchymal.deficit = 3 ∧
      gbmCombined.deficit = 7 ∧
      gbmClassical.deficit < gbmCombined.deficit ∧
      combinedP53Restoration.restoredTopology.deficit ≤
        combinedP53Restoration.topology.deficit := by
  exact
    ⟨gbm_classical_deficit,
      gbm_mesenchymal_deficit,
      gbm_combined_deficit,
      gbm_combined_more_severe_than_classical,
      combined_p53_restoration_improves⟩

end CancerTopology
end Gnosis
