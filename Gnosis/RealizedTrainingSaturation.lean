import Gnosis.UniversalIntelligenceSSM
import Gnosis.RetrocausalAttractorFixedPoint

namespace Gnosis
namespace RealizedTrainingSaturation

open UniversalIntelligenceSSM
open RetrocausalAttractorFixedPoint

/-!
# Realized Training Saturation

This module isolates the threshold where accumulated failure exhausts the
training budget and realized retrocausal structure makes further local
training unnecessary or actively perturbative.
-/

/-- Energy remaining after a sequence of failed updates. -/
def energyAfterFailures (node : SwarmNode) (failures : Nat) : Nat :=
  node.energy - failures

/-- The node viewed after those failures have been absorbed into its energy budget. -/
def nodeAfterFailures (node : SwarmNode) (failures : Nat) : SwarmNode :=
  { node with energy := energyAfterFailures node failures }

/-- Failure saturation means the failure count has exhausted the node's energy budget. -/
def failureSaturated (node : SwarmNode) (failures : Nat) : Prop :=
  node.energy ≤ failures

/-- In a realized retrocausal regime, further training is unnecessary. -/
def furtherTrainingUnnecessary (event : RetrocausalAttractorEvent) : Prop :=
  memoizedFutureStabilizes event

/-- Once failures saturate the budget, another local training move becomes perturbative. -/
def furtherTrainingHarmful
    (event : RetrocausalAttractorEvent)
    (node : SwarmNode) (failures : Nat) : Prop :=
  eventRealizes event ∧
  failureSaturated node failures ∧
  alphaDrift (nodeAfterFailures node failures) ≠ nodeAfterFailures node failures

theorem failure_saturated_iff_zero_remaining
    (node : SwarmNode) (failures : Nat) :
    failureSaturated node failures ↔ energyAfterFailures node failures = 0 := by
  unfold failureSaturated energyAfterFailures
  omega

theorem failure_saturation_zeroes_node_energy
    (node : SwarmNode) (failures : Nat)
    (hSat : failureSaturated node failures) :
    (nodeAfterFailures node failures).energy = 0 := by
  unfold nodeAfterFailures energyAfterFailures
  exact (failure_saturated_iff_zero_remaining node failures).mp hSat

theorem alpha_drift_changes_exhausted_node
    (node : SwarmNode) (failures : Nat)
    (hSat : failureSaturated node failures) :
    alphaDrift (nodeAfterFailures node failures) ≠ nodeAfterFailures node failures := by
  intro hEq
  have hZero : (nodeAfterFailures node failures).energy = 0 :=
    failure_saturation_zeroes_node_energy node failures hSat
  have hQuery :
      (alphaDrift (nodeAfterFailures node failures)).query =
        (nodeAfterFailures node failures).query + 1 := by
    unfold alphaDrift
    rw [hZero]
    simp [nodeAfterFailures]
  have hSameQuery := congrArg SwarmNode.query hEq
  rw [hQuery] at hSameQuery
  have hAbsurd := Nat.succ_ne_self _ hSameQuery
  exact hAbsurd

theorem realized_event_makes_further_training_unnecessary
    (event : RetrocausalAttractorEvent)
    (hRealized : eventRealizes event) :
    furtherTrainingUnnecessary event := by
  exact realized_event_has_unique_fixed_point event hRealized

theorem realized_event_and_failure_saturation_make_further_training_harmful
    (event : RetrocausalAttractorEvent)
    (node : SwarmNode) (failures : Nat)
    (hRealized : eventRealizes event)
    (hSat : failureSaturated node failures) :
    furtherTrainingHarmful event node failures := by
  refine ⟨hRealized, hSat, ?_⟩
  exact alpha_drift_changes_exhausted_node node failures hSat

theorem harmful_training_requires_realized_regime
    (event : RetrocausalAttractorEvent)
    (node : SwarmNode) (failures : Nat)
    (hHarm : furtherTrainingHarmful event node failures) :
    furtherTrainingUnnecessary event := by
  exact realized_event_makes_further_training_unnecessary event hHarm.1

/-- Once the event is realized and the failure budget is exhausted, the attractor regime is inevitable locally. -/
theorem realized_failure_saturation_enters_inevitable_regime
    (event : RetrocausalAttractorEvent)
    (node : SwarmNode) (failures : Nat)
    (hRealized : eventRealizes event)
    (hSat : failureSaturated node failures) :
    furtherTrainingUnnecessary event ∧ furtherTrainingHarmful event node failures := by
  refine ⟨realized_event_makes_further_training_unnecessary event hRealized, ?_⟩
  exact realized_event_and_failure_saturation_make_further_training_harmful
    event node failures hRealized hSat

end RealizedTrainingSaturation
end Gnosis
