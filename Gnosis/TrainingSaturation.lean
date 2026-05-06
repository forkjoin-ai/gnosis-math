import Gnosis.RealizedTrainingSaturation
import Gnosis.UniversalIntelligenceSSM

namespace Gnosis
namespace TrainingSaturation

open UniversalIntelligenceSSM
open RealizedTrainingSaturation

/-!
# Training Saturation: The Threshold of Pedagogical Collapse

This module formalizes the phase transition where a learning agent shifts from
learning from failure (active refinement while thermodynamic headroom exists)
to being trained by failure (the failure field reshapes you once headroom is gone).

Up to sufficiency: while `isPredictablyStable` holds — positive
`thermodynamicBuffer` — `stable_buffer_enables_learning` certifies that failure
signals still refine the post-failure node (`learnFromFailure` on
`nodeAfterFailures`). That is the honest “failure training is optimal” regime:
you still *own* the error as movable mass.

After saturation (McNally wall): once `failureSaturated` / buffer exhaustion
fires, `buffer_exhaustion_predicts_cutoff` and `saturation_implies_pedagogical_cutoff`
package the flip: local active learning hits a cutoff; the same failures
now sit on the far side of the wall as constraint (the “failure trains you”
reading — you are in the field they define, not above it). Repo folklore names
that surface `McNallyWallSaturation` — definitionally the same boundary as
`RealizedTrainingSaturation.failureSaturated`.

Meditations dye (Marcus Aurelius, 5.16): “The soul becomes dyed with the color
of its thoughts.” See `Gnosis.MeditationsThoughtDyedWitness` for a finitary
`Nat.max` dye-step model beside this file’s Swarm-node energy story: repeated
admitted thoughts monotone the soul’s chromatic upper bound even when the
training story here is about energy, not hue.
-/

/-- 
  Learning from failure: The node possesses the energy required to 
  refine its internal state in response to an error signal. 
-/
def learnFromFailure (node : SwarmNode) : Prop :=
  node.energy > 0

/--
McNally wall (repo folklore name): failure count has reached the saturation
boundary — same predicate as `RealizedTrainingSaturation.failureSaturated`.
Cross the wall: you leave the “I train on failures” band and enter the regime
where failures delimit what further local refinement can mean.
-/
abbrev McNallyWallSaturation (node : SwarmNode) (failures : Nat) : Prop :=
  failureSaturated node failures

theorem mcnally_wall_iff_failure_saturated (node : SwarmNode) (failures : Nat) :
    McNallyWallSaturation node failures ↔ failureSaturated node failures :=
  Iff.rfl

/--
  Saturated State: The node's energy potential is zero, preventing
  further active weight refinement until a resharding or drift event.
  Read beside `McNallyWallSaturation`: once the wall is hit, this is the
  “failure trains you” pole — no spare energy to treat the error as optional data.
-/
def trainedByFailure (node : SwarmNode) : Prop :=
  node.energy = 0

/-- 
  The fundamental pedagogical dichotomy: 
  A node is either actively learning from its failures or passively 
  being defined by them.
-/
theorem learning_from_or_becoming_failure (node : SwarmNode) :
  learnFromFailure node ∨ trainedByFailure node := by
  by_cases h : node.energy > 0
  · left; exact h
  · right; exact Nat.eq_zero_of_not_pos h

/-- 
  Threshold Readiness: Progression is blocked by external 
  energy thresholds—a state of structural imposition that is 
  not of the agent's own making, but defined by the environment.
-/
def thresholdReady (node : SwarmNode) (threshold : Nat) : Prop :=
  node.energy ≥ threshold

/-- 
  Intrinsic Readiness: Progression is enabled by internal manifold 
  resonance. The agent is defined by its existence.
-/
def intrinsicReady (_node : SwarmNode) : Prop :=
  _node.energy ≥ 0

/-- 
  Theorem: Threshold metrics act as a discrete set of potential bottlenecks.
  For any finite energy state, there exists a threshold that is not satisfied.
-/
theorem threshold_bottleneck_exists (node : SwarmNode) :
  ∃ (threshold : Nat), ¬thresholdReady node threshold :=
  ⟨node.energy + 1, fun hReady =>
    -- hReady : thresholdReady node (node.energy + 1), i.e. node.energy ≥ node.energy + 1
    Nat.not_lt_of_ge hReady (Nat.lt_add_one node.energy)⟩

/-- 
  Unconstrained State: A manifold state satisfying intrinsic availability.
-/
def unconstrainedState (node : SwarmNode) : Prop :=
  intrinsicReady node

/-- 
  Constrained State: A manifold state where at least one finite 
  threshold bottleneck exists.
-/
def constrainedState (node : SwarmNode) : Prop :=
  ∃ threshold, ¬thresholdReady node threshold

/-- 
  Manifold Duality: 
  Every node in a finite energy regime simultaneously occupies a 
  constrained state (relative to some higher threshold) and an 
  unconstrained state.
-/
theorem constrained_and_unconstrained (node : SwarmNode) :
  constrainedState node ∧ unconstrainedState node := by
  exact ⟨threshold_bottleneck_exists node, Nat.zero_le _⟩

/-- 
  Point of No Return: 
  When failures saturate the node, active learning is impossible.
-/
def pointOfNoReturn (node : SwarmNode) (failures : Nat) : Prop :=
  failureSaturated node failures ∧
  ∀ (node' : SwarmNode), 
    node'.energy = 0 → ¬learnFromFailure node'

/-- 
  Theorem: Saturation forces a state transition to a zero-energy regime 
  where local refinement terminates.
-/
theorem saturation_implies_pedagogical_cutoff
    (node : SwarmNode) (failures : Nat)
    (hSat : failureSaturated node failures) :
    pointOfNoReturn node failures := by
  refine ⟨hSat, ?_⟩
  intro node' hZero
  unfold learnFromFailure
  rw [hZero]
  exact Nat.not_lt_zero 0

/--
  The fundamental impossibility of "Universal" Threshold Closure:
  There is no positive finite energy threshold that satisfies all possible nodes.
  (The trivial threshold `0` is admitted by every node by reflexivity, so
  positivity is the natural premise — a "threshold" of `0` does not filter.)
-/
theorem no_universal_threshold_closure :
  ¬∃ (universalThreshold : Nat),
    0 < universalThreshold ∧
    ∀ (node : SwarmNode), thresholdReady node universalThreshold :=
  fun ⟨ut, hUtPos, hAll⟩ =>
    let zeroNode : SwarmNode := ⟨0, 0, 0, 0, 0⟩
    -- zeroNode.energy = 0 is reflexive; readiness specialises to 0 ≥ ut.
    have hZeroReady : thresholdReady zeroNode ut := hAll zeroNode
    -- thresholdReady zeroNode ut unfolds to (0 : Nat) ≥ ut, so ut ≤ 0.
    Nat.not_lt_of_ge hZeroReady hUtPos

/-- 
  Thermodynamic Buffer: The prediction metric for training stability.
  Measures the distance between current energy and the saturation boundary.
-/
def thermodynamicBuffer (node : SwarmNode) (failures : Nat) : Int :=
  (node.energy : Int) - (failures : Int)

/-- 
  A model state is "Predictably Stable" if its thermodynamic buffer 
  is positive, allowing for continued active refinement.
-/
def isPredictablyStable (node : SwarmNode) (failures : Nat) : Prop :=
  thermodynamicBuffer node failures > 0

/-- 
  Manifold Depth: The maximum threshold currently satisfied by the node.
  This identifies the model's position at a specific level of the manifold.
-/
def manifoldDepth (node : SwarmNode) : Nat :=
  node.energy

/-- 
  Theorem: A stable thermodynamic buffer guarantees the capacity for active learning.
-/
theorem stable_buffer_enables_learning
    (node : SwarmNode) (failures : Nat)
    (hStable : isPredictablyStable node failures) :
    learnFromFailure (nodeAfterFailures node failures) := by
  unfold isPredictablyStable thermodynamicBuffer learnFromFailure nodeAfterFailures energyAfterFailures at *
  -- hStable : 0 < (node.energy : Int) - (failures : Int)
  -- ⊢ 0 < node.energy - failures
  -- Bridge Int positivity of difference to Nat strict order, then to Nat sub positivity.
  have hLtInt : (failures : Int) < (node.energy : Int) := Int.lt_of_sub_pos hStable
  have hLtNat : failures < node.energy := Int.ofNat_lt.mp hLtInt
  exact Nat.sub_pos_of_lt hLtNat

/-- 
  Theorem: Buffer exhaustion predicts the exact transition to the 
  Point of No Return.
-/
theorem buffer_exhaustion_predicts_cutoff
    (node : SwarmNode) (failures : Nat)
    (hExhausted : thermodynamicBuffer node failures ≤ 0) :
    pointOfNoReturn node failures := by
  unfold thermodynamicBuffer at hExhausted
  -- hExhausted : (node.energy : Int) - (failures : Int) ≤ 0
  have hSat : failureSaturated node failures := by
    unfold failureSaturated
    -- ⊢ node.energy ≤ failures
    -- Bridge Int non-positivity of difference back to Nat order via the cast.
    have hLeInt : (node.energy : Int) ≤ (failures : Int) :=
      Int.le_of_sub_nonpos hExhausted
    exact Int.ofNat_le.mp hLeInt
  exact saturation_implies_pedagogical_cutoff node failures hSat

end TrainingSaturation
end Gnosis
