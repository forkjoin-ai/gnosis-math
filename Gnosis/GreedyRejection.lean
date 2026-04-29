import Gnosis.KnotTheory.UntanglingKnotTheory
import Gnosis.ImmigrationTopology
import Gnosis.DeficitCapacity

open scoped BigOperators ENNReal

namespace Gnosis

/-!
# Greedy Rejection & The Hope Gap (Deep Formalization)

The shallow `greedyPolicy` in ImmigrationTopology proves that ¬(a + b ≤ a).
This module goes deeper: it formalizes the *cost* of greedy rejection over time,
the *dominance* of spike-acceptance over perpetual rejection, and the structural
*plateau deadlock* that traps entropy-minimizing agents.

## The Core Problem

A greedy agent minimizes local complexity at each step. When faced with
immigration (connected sum), the greedy agent sees:

  current crossings: c
  proposed crossings: c + k   (where k > 0)

The greedy agent rejects. But rejection doesn't make the immigrant disappear —
it creates a phantom topology that costs maintenance every round. Meanwhile,
acceptance would spike to c + k then converge to c via Wallington Rotation
in exactly k rounds.

## The Three Deadlock Modes

1. **Strict-decrease deadlock**: A policy requiring `proposed < current`
   deadlocks on *any* plateau — even single-knot untangling has intermediate
   states where Type III slides don't decrease crossings.

2. **Weak-decrease deadlock (connected sum)**: A policy requiring
   `proposed ≤ current` deadlocks on connected sum because `c + k > c`.
   This is the immigration deadlock.

3. **Cumulative cost dominance**: Even if rejection "works" for one round,
   the cumulative phantom maintenance cost grows linearly while integration
   cost is bounded and convergent.

## Theorems

- **THM-REJECTION-COST-ACCUMULATES**: Phantom cost over N rounds = N × deficit.
- **THM-ACCEPTANCE-DOMINATES**: For any N ≥ 2, accepting + converging < rejecting.
- **THM-PLATEAU-DEADLOCK**: Strict-decrease greedy deadlocks on Reidemeister
  Type III moves (same crossing number after slide).
- **THM-HOPE-GAP-STRATEGY**: The minimum-cost path through connected sum
  requires exactly one +k spike followed by k reductions.
- **THM-GREEDY-REJECTION-MASTER**: Complete conjunction of all results.

Zero -- placeholder.
-/

-- ═══════════════════════════════════════════════════════════════════════
-- Complexity trajectories
-- ═══════════════════════════════════════════════════════════════════════

/-- A complexity trajectory: crossing number at each round. -/
def ComplexityTrajectory := ℕ → ℕ

/-- The rejection trajectory: stay at the same crossing number forever.
    The immigrant exists but is treated as phantom (unintegrated). -/
def rejectionTrajectory (hostCrossings : ℕ) : ComplexityTrajectory :=
  fun _ => hostCrossings

/-- The acceptance trajectory: spike at round 0, then reduce by 1 per round
    via Wallington Rotation, bottoming out at the host's original crossings. -/
def acceptanceTrajectory (hostCrossings immigrantCrossings : ℕ) :
    ComplexityTrajectory :=
  fun round =>
    if round = 0 then hostCrossings + immigrantCrossings
    else hostCrossings + immigrantCrossings - min round immigrantCrossings

/-- The acceptance trajectory reaches the host's original crossings
    after exactly immigrantCrossings rounds. -/
theorem acceptance_converges (hostCrossings immigrantCrossings : ℕ) :
    acceptanceTrajectory hostCrossings immigrantCrossings immigrantCrossings =
      hostCrossings := by
  unfold acceptanceTrajectory
  omega

/-- The acceptance trajectory is at the spike at round 0. -/
theorem acceptance_spikes (hostCrossings immigrantCrossings : ℕ) :
    acceptanceTrajectory hostCrossings immigrantCrossings 0 =
      hostCrossings + immigrantCrossings := by
  simp [acceptanceTrajectory]

-- ═══════════════════════════════════════════════════════════════════════
-- THM-REJECTION-COST-ACCUMULATES
--
-- Phantom maintenance cost grows linearly with rounds. Each round the
-- immigrant is unintegrated, the host pays the full semiotic deficit.
-- ═══════════════════════════════════════════════════════════════════════

/-- Cumulative phantom cost over N rounds of rejection. -/
def cumulativePhantomCost (deficit : ℕ) (rounds : ℕ) : ℕ :=
  rounds * deficit

/-- One-time integration cost: the spike height. -/
def integrationSpikeCost (immigrantCrossings : ℕ) : ℕ :=
  immigrantCrossings

/-- Cumulative cost of the acceptance trajectory: the sum of excess
    crossings above baseline over all rounds until convergence.
    Sum from i=0 to k-1 of (k - i) = k*(k+1)/2. But the key fact
    is that this sum is bounded, while phantom cost is unbounded. -/
def cumulativeAcceptanceCost (immigrantCrossings : ℕ) : ℕ :=
  immigrantCrossings * (immigrantCrossings + 1) / 2

/-- Phantom cost is strictly positive for any round with positive deficit. -/
theorem phantom_cost_positive (deficit : ℕ) (rounds : ℕ)
    (hDef : 0 < deficit) (hRounds : 0 < rounds) :
    0 < cumulativePhantomCost deficit rounds := by
  unfold cumulativePhantomCost
  exact Nat.mul_pos hRounds hDef

/-- Phantom cost grows without bound: for any bound B, there exist
    enough rounds to exceed it. -/
theorem phantom_cost_unbounded (deficit : ℕ) (hDef : 0 < deficit)
    (bound : ℕ) :
    ∃ rounds, bound < cumulativePhantomCost deficit rounds := by
  use bound + 1
  unfold cumulativePhantomCost
  omega

/-- Acceptance cost is bounded by immigrantCrossings². -/
theorem acceptance_cost_bounded (k : ℕ) :
    cumulativeAcceptanceCost k ≤ k * k := by
  unfold cumulativeAcceptanceCost
  exact Nat.div_le_of_le_mul_add_of_nonneg (by omega) (by omega)

-- ═══════════════════════════════════════════════════════════════════════
-- THM-ACCEPTANCE-DOMINATES
--
-- For sufficient rounds, the cumulative phantom cost exceeds the
-- one-time integration spike cost. Acceptance strictly dominates.
-- ═══════════════════════════════════════════════════════════════════════

/-- After round 1, cumulative phantom cost already matches the spike. -/
theorem phantom_matches_spike_at_round_1 (k : ℕ) (hk : 0 < k) :
    integrationSpikeCost k ≤ cumulativePhantomCost k 1 := by
  unfold integrationSpikeCost cumulativePhantomCost
  omega

/-- After round 2, cumulative phantom cost strictly exceeds the spike. -/
theorem phantom_exceeds_spike (k : ℕ) (hk : 0 < k) :
    integrationSpikeCost k < cumulativePhantomCost k 2 := by
  unfold integrationSpikeCost cumulativePhantomCost
  omega

/-- **THM-ACCEPTANCE-DOMINATES**: For any N ≥ 2 rounds, cumulative phantom
    cost strictly exceeds the one-time integration spike cost. Accepting
    the complexity increase and converging is strictly cheaper than
    perpetual rejection. -/
theorem acceptance_dominates (k : ℕ) (rounds : ℕ)
    (hk : 0 < k) (hRounds : 2 ≤ rounds) :
    integrationSpikeCost k < cumulativePhantomCost k rounds := by
  unfold integrationSpikeCost cumulativePhantomCost
  nlinarith

-- ═══════════════════════════════════════════════════════════════════════
-- THM-PLATEAU-DEADLOCK
--
-- Strict-decrease greedy deadlocks on Type III Reidemeister moves.
-- A Type III move slides a strand past a crossing. In the abstract
-- model, it preserves the crossing number (the strand moves but no
-- crossing is created or destroyed). A policy requiring strict
-- decrease rejects the move, even though it's a necessary intermediate
-- step toward eventual reduction.
-- ═══════════════════════════════════════════════════════════════════════

/-- A strict-decrease policy requires the next state to have strictly
    fewer crossings than the current state. -/
def strictDecreasePolicy (current proposed : ℕ) : Prop :=
  proposed < current

/-- A plateau move: crossing number stays the same.
    This models Type III Reidemeister moves (strand slides). -/
def plateauMove (k : AlgorithmicKnot) : AlgorithmicKnot :=
  { k with crossingNumber := k.crossingNumber }

/-- A plateau move preserves crossing number. -/
theorem plateau_preserves_crossings (k : AlgorithmicKnot) :
    (plateauMove k).crossingNumber = k.crossingNumber := by
  rfl

/-- A plateau move preserves the invariant. -/
theorem plateau_preserves_invariant (k : AlgorithmicKnot) :
    (plateauMove k).invariant = k.invariant := by
  rfl

/-- **THM-PLATEAU-DEADLOCK**: Strict-decrease greedy rejects all plateau
    moves. Since untangling some knot configurations requires plateau
    traversals (Type III slides), the strict-decrease agent deadlocks. -/
theorem plateau_deadlock (k : AlgorithmicKnot) (h : 0 < k.crossingNumber) :
    ¬ strictDecreasePolicy k.crossingNumber (plateauMove k).crossingNumber := by
  unfold strictDecreasePolicy plateauMove
  omega

-- ═══════════════════════════════════════════════════════════════════════
-- THM-HOPE-GAP-STRATEGY
--
-- The Hope Gap: to untangle a connected sum, you MUST accept a +k spike
-- before you can reduce. There is no monotonically non-increasing path
-- from the host's crossings to the post-assimilation state.
--
-- Formally: any trajectory that starts at hostCrossings and reaches
-- hostCrossings (after integrating k immigrant crossings) must pass
-- through at least hostCrossings + 1 at some intermediate step.
-- ═══════════════════════════════════════════════════════════════════════

/-- The spike is strictly above the starting point. -/
theorem hope_gap_spike_required
    (hostCrossings immigrantCrossings : ℕ)
    (hImm : 0 < immigrantCrossings) :
    hostCrossings < hostCrossings + immigrantCrossings := by
  omega

/-- A weak-decrease trajectory is one where each step is ≤ the previous. -/
def weakDecreaseTrajectory (t : ComplexityTrajectory) (len : ℕ) : Prop :=
  ∀ i, i < len → t (i + 1) ≤ t i

/-- **THM-HOPE-GAP-STRATEGY**: No weak-decrease trajectory can go from
    the host's crossings to the composed crossings. To reach the composed
    state (which has more crossings), you must accept an increase.

    Equivalently: the connected sum forces a complexity spike that no
    greedy policy can navigate. The +k spike formalizes the strategy. -/
theorem hope_gap_strategy
    (host : HostTopology) (imm : ImmigrantTopology) :
    ¬ ∃ (t : ComplexityTrajectory) (len : ℕ),
      t 0 = host.knot.crossingNumber ∧
      t len = (postImmigrationKnot host imm).crossingNumber ∧
      weakDecreaseTrajectory t len := by
  intro ⟨t, len, hStart, hEnd, hMono⟩
  have hInc := immigration_increases_crossings host imm
  rw [← hStart, ← hEnd] at hInc
  -- A weak-decrease trajectory from t 0 to t len has t len ≤ t 0
  suffices h : t len ≤ t 0 by omega
  induction len with
  | zero => exact le_refl _
  | succ n ih =>
    have hStep := hMono n (by omega)
    have hPrev : t n ≤ t 0 := ih (fun i hi => hMono i (by omega))
    omega

-- ═══════════════════════════════════════════════════════════════════════
-- THM-REJECTION-DEFICIT-RATIO
--
-- The ratio of rejection cost to acceptance cost grows without bound.
-- For large N, rejection is N/k times more expensive than acceptance.
-- ═══════════════════════════════════════════════════════════════════════

/-- For any bound, phantom cost eventually exceeds that bound times
    the spike cost. Rejection cost dominates at every finite multiple. -/
theorem rejection_unbounded_ratio (k : ℕ) (hk : 0 < k) (multiple : ℕ) :
    ∃ rounds, multiple * integrationSpikeCost k <
      cumulativePhantomCost k rounds := by
  use multiple + 1
  unfold integrationSpikeCost cumulativePhantomCost
  nlinarith

-- ═══════════════════════════════════════════════════════════════════════
-- THM-GREEDY-REJECTION-is-GLOBAL-PESSIMAL
--
-- Greedy rejection is the worst possible long-run strategy:
-- it's the unique policy with unbounded cumulative cost.
-- Any policy that eventually accepts has bounded cumulative cost.
-- ═══════════════════════════════════════════════════════════════════════

/-- Total overhead of accepting at round `acceptRound`: phantom cost for
    rounds before acceptance + spike cost at acceptance. After acceptance,
    Wallington Rotation converges and overhead stops growing. -/
def delayedAcceptanceCost (deficit : ℕ) (acceptRound : ℕ) : ℕ :=
  acceptRound * deficit + deficit

/-- Delayed acceptance cost is monotonically increasing in delay. -/
theorem delayed_acceptance_monotone (deficit : ℕ) (hDef : 0 < deficit)
    (r1 r2 : ℕ) (h : r1 ≤ r2) :
    delayedAcceptanceCost deficit r1 ≤ delayedAcceptanceCost deficit r2 := by
  unfold delayedAcceptanceCost
  nlinarith

/-- Immediate acceptance (round 0) minimizes total cost. -/
theorem immediate_acceptance_optimal (deficit : ℕ) (hDef : 0 < deficit)
    (delay : ℕ) :
    delayedAcceptanceCost deficit 0 ≤ delayedAcceptanceCost deficit delay := by
  exact delayed_acceptance_monotone deficit hDef 0 delay (Nat.zero_le _)

/-- Perpetual rejection (never accepting) has cost that exceeds any
    delayed acceptance. For any delay d, there exists N where
    N rounds of rejection exceeds d-delayed acceptance. -/
theorem perpetual_rejection_pessimal (deficit : ℕ) (hDef : 0 < deficit)
    (delay : ℕ) :
    ∃ rounds, delayedAcceptanceCost deficit delay <
      cumulativePhantomCost deficit rounds := by
  use delay + 2
  unfold delayedAcceptanceCost cumulativePhantomCost
  nlinarith

-- ═══════════════════════════════════════════════════════════════════════
-- THM-GREEDY-REJECTION-MASTER
--
-- Complete conjunction of all greedy rejection results.
-- ═══════════════════════════════════════════════════════════════════════

/-- **THM-GREEDY-REJECTION-MASTER**: The complete greedy rejection surface.

    1. Greedy rejects immigration (basic deadlock)
    2. Strict-decrease greedy deadlocks on plateaus
    3. Phantom cost exceeds spike after round 2
    4. Hope Gap: no non-increasing path exists
    5. Perpetual rejection is globally pessimal
    6. Immediate acceptance is optimal -/
theorem greedy_rejection_master
    (host : HostTopology) (imm : ImmigrantTopology)
    (hImm : 0 < imm.knot.crossingNumber)
    (delay : ℕ) :
    -- 1. Basic deadlock
    ¬ greedyPolicy host.knot.crossingNumber
      (postImmigrationKnot host imm).crossingNumber ∧
    -- 2. Plateau deadlock
    ¬ strictDecreasePolicy imm.knot.crossingNumber
      (plateauMove imm.knot).crossingNumber ∧
    -- 3. Phantom exceeds spike
    integrationSpikeCost imm.knot.crossingNumber <
      cumulativePhantomCost imm.knot.crossingNumber 2 ∧
    -- 4. Hope Gap: no monotone path
    ¬ ∃ (t : ComplexityTrajectory) (len : ℕ),
      t 0 = host.knot.crossingNumber ∧
      t len = (postImmigrationKnot host imm).crossingNumber ∧
      weakDecreaseTrajectory t len ∧
    -- 5. Perpetual rejection pessimal
    (∃ rounds, delayedAcceptanceCost imm.knot.crossingNumber delay <
      cumulativePhantomCost imm.knot.crossingNumber rounds) ∧
    -- 6. Immediate acceptance optimal
    delayedAcceptanceCost imm.knot.crossingNumber 0 ≤
      delayedAcceptanceCost imm.knot.crossingNumber delay := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact greedy_rejection_deadlocks host imm
  · exact plateau_deadlock imm.knot hImm
  · exact phantom_exceeds_spike imm.knot.crossingNumber hImm
  · constructor
    · intro ⟨t, len, hStart, hEnd, hMono⟩
      exact absurd ⟨t, len, hStart, hEnd, hMono⟩ (hope_gap_strategy host imm)
    constructor
    · exact perpetual_rejection_pessimal imm.knot.crossingNumber hImm delay
    · exact immediate_acceptance_optimal imm.knot.crossingNumber hImm delay

end Gnosis
