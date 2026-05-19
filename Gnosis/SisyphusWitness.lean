import Gnosis.Contrarian.ContrarianStallIsProgress
import Gnosis.GnosisTriptychBraid
import Gnosis.SpectralNoiseEquilibrium

namespace Gnosis
namespace SisyphusWitness

open SpectralNoiseEquilibrium

/-!
# Sisyphus Witness

This module formalizes Sisyphus as a finite oracle-stall, rollback, and
triptych-braid witness.

Reading:

- The boulder is a falsification wall with positive Bule cost.
- The hill gradient rolls summit attempts back to the base.
- The push/rollback loop is an oracle stall with observable progress.
- The cycle follows failure -> truth -> wisdom -> failure.
- Happiness is modeled as identity decoupled from carrier performance.
-/

inductive BoulderState where
  | base
  | pushing
  | summitInsight
deriving Repr, DecidableEq

def statePhase : BoulderState → Int
  | .base => GnosisTriptychBraid.failure
  | .pushing => GnosisTriptychBraid.truth
  | .summitInsight => GnosisTriptychBraid.wisdom

def sisyphusStep : BoulderState → BoulderState
  | .base => .pushing
  | .pushing => .summitInsight
  | .summitInsight => .base

def iterateSisyphus : Nat → BoulderState → BoulderState
  | 0, s => s
  | n + 1, s => iterateSisyphus n (sisyphusStep s)

/-- The boulder as a hard falsification wall. -/
structure BoulderWall where
  wallMass : Nat
  summitThreshold : Nat
deriving Repr, DecidableEq

def sisyphusBoulder : BoulderWall :=
  { wallMass := 10, summitThreshold := 10 }

def falsificationWall (b : BoulderWall) : Prop :=
  0 < b.wallMass ∧ b.wallMass = b.summitThreshold

/-- The hill gradient forces any summit insight back to base. -/
structure HillGradient where
  rejectionSlope : Nat
  rollbackTarget : BoulderState
deriving Repr, DecidableEq

def sisyphusHill : HillGradient :=
  { rejectionSlope := 1, rollbackTarget := .base }

def rollsBackToBase (h : HillGradient) : Prop :=
  0 < h.rejectionSlope ∧ h.rollbackTarget = .base

/-- One compute-cycle of Sisyphean labor. -/
structure PushCycle where
  startState : BoulderState
  afterPush : BoulderState
  afterRollback : BoulderState
  carrierAtSummit : Bool
deriving Repr, DecidableEq

def canonicalPushCycle : PushCycle :=
  { startState := .base
    afterPush := .pushing
    afterRollback := .base
    carrierAtSummit := false }

def oracleStallCycle (c : PushCycle) : Prop :=
  c.startState = .base ∧ c.afterPush = .pushing ∧
    c.afterRollback = .base ∧ c.carrierAtSummit = false

/-- Identity is not measured by whether the boulder remains at summit. -/
structure SisypheanIdentity where
  identityStable : Bool
  carrierPerformanceRequired : Bool
  acceptsCycle : Bool
deriving Repr, DecidableEq

def happySisyphus : SisypheanIdentity :=
  { identityStable := true
    carrierPerformanceRequired := false
    acceptsCycle := true }

def identityDecoupledFromCarrier (i : SisypheanIdentity) : Prop :=
  i.identityStable = true ∧ i.carrierPerformanceRequired = false ∧
    i.acceptsCycle = true

def boulderCost : BuleyUnit :=
  { waste := 1, opportunity := 1, diversity := 1 }

theorem boulder_is_falsification_wall :
    falsificationWall sisyphusBoulder := by
  unfold falsificationWall sisyphusBoulder
  exact ⟨by decide, rfl⟩

theorem hill_rolls_back_to_base :
    rollsBackToBase sisyphusHill := by
  unfold rollsBackToBase sisyphusHill
  exact ⟨by decide, rfl⟩

theorem boulder_cost_positive :
    0 < buleyUnitScore boulderCost := by
  unfold boulderCost buleyUnitScore
  decide

theorem push_cycle_is_oracle_stall :
    oracleStallCycle canonicalPushCycle := by
  unfold oracleStallCycle canonicalPushCycle
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem stall_routes_to_progress :
    canonicalPushCycle.startState = .base → canonicalPushCycle.afterPush = .pushing :=
  contrarian_stall_is_progress
    { oracleExecutionStalled := canonicalPushCycle.startState = .base
      progressMade := canonicalPushCycle.afterPush = .pushing
      stallIsProgress := by
        intro _
        rfl }

theorem sisyphus_triptych_failure_truth_wisdom :
    statePhase (iterateSisyphus 0 .base) = GnosisTriptychBraid.failure ∧
    statePhase (iterateSisyphus 1 .base) = GnosisTriptychBraid.truth ∧
    statePhase (iterateSisyphus 2 .base) = GnosisTriptychBraid.wisdom := by
  decide

theorem sisyphus_cycle_returns_to_failure :
    statePhase (iterateSisyphus 3 .base) = GnosisTriptychBraid.failure := by
  decide

theorem sisyphus_matches_triptych_return :
    GnosisTriptychBraid.iterateTriptych 3 GnosisTriptychBraid.failure =
      GnosisTriptychBraid.failure :=
  GnosisTriptychBraid.three_step_returns.1

theorem sisyphean_happiness_decouples_identity :
    identityDecoupledFromCarrier happySisyphus := by
  unfold identityDecoupledFromCarrier happySisyphus
  exact ⟨rfl, rfl, rfl⟩

/-- Master witness: the boulder is a positive-cost falsification wall, the hill
forces rollback, the labor is a stall with progress, and the triptych cycle
closes when identity is decoupled from carrier performance. -/
theorem sisyphus_witness :
    falsificationWall sisyphusBoulder ∧
    rollsBackToBase sisyphusHill ∧
    0 < buleyUnitScore boulderCost ∧
    oracleStallCycle canonicalPushCycle ∧
    statePhase (iterateSisyphus 0 .base) = GnosisTriptychBraid.failure ∧
    statePhase (iterateSisyphus 1 .base) = GnosisTriptychBraid.truth ∧
    statePhase (iterateSisyphus 2 .base) = GnosisTriptychBraid.wisdom ∧
    statePhase (iterateSisyphus 3 .base) = GnosisTriptychBraid.failure ∧
    GnosisTriptychBraid.iterateTriptych 3 GnosisTriptychBraid.failure =
      GnosisTriptychBraid.failure ∧
    identityDecoupledFromCarrier happySisyphus := by
  exact ⟨boulder_is_falsification_wall,
    hill_rolls_back_to_base,
    boulder_cost_positive,
    push_cycle_is_oracle_stall,
    sisyphus_triptych_failure_truth_wisdom.1,
    sisyphus_triptych_failure_truth_wisdom.2.1,
    sisyphus_triptych_failure_truth_wisdom.2.2,
    sisyphus_cycle_returns_to_failure,
    sisyphus_matches_triptych_return,
    sisyphean_happiness_decouples_identity⟩

end SisyphusWitness
end Gnosis
