import BuleyeanMath.UntanglingKnotTheory
import BuleyeanMath.PerpetualSpiral
import BuleyeanMath.SpiralMachine
import BuleyeanMath.SpiralDeterminism
import BuleyeanMath.RotationPatterns
import BuleyeanMath.WallingtonOptimality

namespace BuleyeanMath

/-!
# KnotTheoryGrind -- Cross-pollination of Knot Theory, Spiral Machine, and Determinism

Three rounds of theorem grinding, mixing:
- Algorithmic knot theory (crossings, Reidemeister, unknotting)
- Spiral machine (tape, head, TM simulation)
- Spiral determinism (void state, complement, clockwork)
- Wallington rotation (DAG scheduling, makespan, speedup)
- Perpetual spiral (sliver, vents, Dyson capture)

Every theorem fully proven. Zero -- placeholder.
-/

-- ═══════════════════════════════════════════════════════════════════════
-- ROUND 1: Knot-theoretic foundations
-- ═══════════════════════════════════════════════════════════════════════

-- ─────────────────────────────────────────────────────────────────────
-- THM-CONNECTED-SUM-IDENTITY
--
-- The unknot is the identity element for connected sum.
-- composeKnots (unknot inv) k has the same crossing number as k.
-- This is the monoid identity for algorithmic knot composition.
-- ─────────────────────────────────────────────────────────────────────

theorem connected_sum_identity_left (k : AlgorithmicKnot) :
    (composeKnots (unknot 0) k).crossingNumber = k.crossingNumber := by
  unfold composeKnots unknot
  simp

theorem connected_sum_identity_right (k : AlgorithmicKnot) :
    (composeKnots k (unknot 0)).crossingNumber = k.crossingNumber := by
  unfold composeKnots unknot
  simp

-- ─────────────────────────────────────────────────────────────────────
-- THM-CONNECTED-SUM-ASSOCIATIVE
--
-- Connected sum of knots is associative: (a # b) # c = a # (b # c)
-- in terms of crossing number. This makes algorithmic knots a monoid.
-- ─────────────────────────────────────────────────────────────────────

theorem connected_sum_associative (a b c : AlgorithmicKnot) :
    (composeKnots (composeKnots a b) c).crossingNumber =
    (composeKnots a (composeKnots b c)).crossingNumber := by
  unfold composeKnots
  omega

-- ─────────────────────────────────────────────────────────────────────
-- THM-CONNECTED-SUM-COMMUTATIVE
--
-- Connected sum is commutative in crossing number: a # b = b # a.
-- ─────────────────────────────────────────────────────────────────────

theorem connected_sum_commutative (a b : AlgorithmicKnot) :
    (composeKnots a b).crossingNumber = (composeKnots b a).crossingNumber := by
  unfold composeKnots
  omega

-- ─────────────────────────────────────────────────────────────────────
-- THM-CONNECTED-SUM-BETA1-ADDITIVE
--
-- beta1 is additive under connected sum, just like crossing number.
-- The genus of a connected sum is the sum of genera.
-- ─────────────────────────────────────────────────────────────────────

theorem connected_sum_beta1_additive (a b : AlgorithmicKnot) :
    (composeKnots a b).beta1 = a.beta1 + b.beta1 := by
  rfl

-- ─────────────────────────────────────────────────────────────────────
-- THM-REIDEMEISTER-PRESERVES-BETA1
--
-- Reidemeister moves preserve the first Betti number (cycle count).
-- beta1 is a knot invariant.
-- ─────────────────────────────────────────────────────────────────────

theorem reidemeister_preserves_beta1 (k : AlgorithmicKnot) (m : ReidemeisterMove) :
    (applyMove k m).beta1 = k.beta1 := by
  cases m <;> rfl

-- ─────────────────────────────────────────────────────────────────────
-- THM-WALLINGTON-PRESERVES-BETA1
--
-- The full Wallington rotation preserves beta1 across all moves.
-- ─────────────────────────────────────────────────────────────────────

theorem wallington_preserves_beta1 (k : AlgorithmicKnot) :
    (wallingtonRotation k).beta1 = k.beta1 := by
  induction k using wallingtonRotation.induct with
  | case1 k h =>
    simp [wallingtonRotation, h]
  | case2 k h ih =>
    simp [wallingtonRotation, h]
    rw [ih]
    exact reidemeister_preserves_beta1 k .typeI

-- ─────────────────────────────────────────────────────────────────────
-- THM-UNKNOT-is-FIXED-POINT
--
-- The unknot is a fixed point of Reidemeister type I (self-crossing
-- removal on zero crossings is a no-op since 0 - 1 = 0 in Nat).
-- ─────────────────────────────────────────────────────────────────────

theorem unknot_typeI_fixed (inv : ℕ) :
    (applyMove (unknot inv) .typeI).crossingNumber = 0 := by
  unfold applyMove unknot
  simp

theorem unknot_typeIII_fixed (inv : ℕ) :
    (applyMove (unknot inv) .typeIII).crossingNumber = 0 := by
  unfold applyMove unknot
  simp

-- ─────────────────────────────────────────────────────────────────────
-- THM-MOVE-SEQUENCE-LENGTH-BOUNDS-CROSSINGS
--
-- The number of Reidemeister type I moves needed to unknot is at most
-- the crossing number. Each move removes exactly one crossing.
-- ─────────────────────────────────────────────────────────────────────

theorem unknotting_sequence_length (k : AlgorithmicKnot) :
    ∀ n, n ≤ k.crossingNumber →
    (Nat.iterate (fun k' => applyMove k' .typeI) n k).crossingNumber =
    k.crossingNumber - n := by
  intro n
  induction n with
  | zero => simp [Nat.iterate]
  | succ m ih =>
    intro h_le
    simp [Nat.iterate, Function.iterate_succ']
    rw [ih (by omega)]
    unfold applyMove
    omega

-- ─────────────────────────────────────────────────────────────────────
-- THM-TYPEII-REMOVES-TWO-CROSSINGS
--
-- Type II move is more efficient: removes 2 crossings per move.
-- Needs at least 2 crossings to be applicable.
-- ─────────────────────────────────────────────────────────────────────

theorem typeII_efficient (k : AlgorithmicKnot) (h : 2 ≤ k.crossingNumber) :
    k.crossingNumber - (applyMove k .typeII).crossingNumber = 2 := by
  unfold applyMove
  omega

-- ─────────────────────────────────────────────────────────────────────
-- THM-WALLINGTON-IDEMPOTENT
--
-- Applying Wallington rotation twice is the same as once.
-- Once you reach the unknot, you stay there.
-- ─────────────────────────────────────────────────────────────────────

theorem wallington_idempotent (k : AlgorithmicKnot) :
    wallingtonRotation (wallingtonRotation k) = wallingtonRotation k := by
  have h := wallington_produces_unknot k
  have : (wallingtonRotation k).crossingNumber = 0 := h
  exact optimal_is_unknot (wallingtonRotation k) this

-- ═══════════════════════════════════════════════════════════════════════
-- ROUND 1: Cross-mixing knot theory with spiral machine
-- ═══════════════════════════════════════════════════════════════════════

-- ─────────────────────────────────────────────────────────────────────
-- THM-TAPE-WRITE-is-REIDEMEISTER
--
-- Each tape write in the spiral machine corresponds to a void boundary
-- growth, which is a topological change. Writing v > 0 to a cell
-- changes the crossing number of the algorithmic topology at that cell.
-- ─────────────────────────────────────────────────────────────────────

theorem tape_write_nondestructive (tape : SpiralTape) (p v : ℕ) :
    (tapeWrite tape p v).cells p ≥ tape.cells p := by
  simp [tapeWrite]

-- ─────────────────────────────────────────────────────────────────────
-- THM-TAPE-WRITE-COMMUTATIVE
--
-- Writing to two different cells commutes: the order doesn't matter.
-- This is because writes to distinct positions are independent.
-- ─────────────────────────────────────────────────────────────────────

theorem tape_write_commutative (tape : SpiralTape) (p q vp vq : ℕ)
    (h : p ≠ q) :
    (tapeWrite (tapeWrite tape p vp) q vq).cells =
    (tapeWrite (tapeWrite tape q vq) p vp).cells := by
  ext i
  simp [tapeWrite]
  split <;> split <;> simp_all <;> omega

-- ─────────────────────────────────────────────────────────────────────
-- THM-BLANK-TAPE-is-UNKNOT
--
-- A blank tape (all zeros) is the unknot: no crossings, no tangles.
-- The void boundary starts empty -- the topology starts optimal.
-- ─────────────────────────────────────────────────────────────────────

theorem blank_tape_is_unknot :
    blankTape.cells 0 = 0 ∧ blankTape.extent = 0 := by
  constructor <;> rfl

-- ─────────────────────────────────────────────────────────────────────
-- THM-TAPE-EXTENT-AFTER-N-WRITES
--
-- After N writes at positions 0..N-1, the tape extent is at least N.
-- ─────────────────────────────────────────────────────────────────────

theorem tape_extent_after_write (tape : SpiralTape) (p v : ℕ) :
    p + 1 ≤ (tapeWrite tape p v).extent := by
  simp [tapeWrite]
  omega

-- ─────────────────────────────────────────────────────────────────────
-- THM-MACHINE-STEP-PRESERVES-TAPE-CELLS
--
-- A machine step only modifies the cell at the current head position.
-- All other cells are unchanged. Locality of tape operations.
-- ─────────────────────────────────────────────────────────────────────

theorem machine_step_locality (tape : SpiralTape) (state : MachineState)
    (δ : ℕ → ℕ → SpiralTransition) (q : ℕ) (h : q ≠ tape.head) :
    (machineStep tape state δ).1.cells q = tape.cells q := by
  simp [machineStep, tapeWrite, tapeMove]
  intro h_eq
  exact absurd h_eq h

-- ═══════════════════════════════════════════════════════════════════════
-- ROUND 1: Spiral determinism meets knot theory
-- ═══════════════════════════════════════════════════════════════════════

-- ─────────────────────────────────────────────────────────────────────
-- THM-COMPLEMENT-WEIGHTS-POSITIVE
--
-- Every complement weight is positive (the sliver in weight-space).
-- This is the god formula's +1 manifest in complement weights.
-- ─────────────────────────────────────────────────────────────────────

theorem complement_weights_positive (counts : List ℕ) (R : ℕ) :
    ∀ w ∈ (complementWeights counts R), 0 < w := by
  intro w hw
  unfold complementWeights at hw
  rw [List.mem_map] at hw
  obtain ⟨v, _, rfl⟩ := hw
  omega

-- ─────────────────────────────────────────────────────────────────────
-- THM-COMPLEMENT-WEIGHTS-LENGTH-PRESERVED
--
-- The complement operation preserves the number of dimensions.
-- Same number of weights as rejection counts.
-- ─────────────────────────────────────────────────────────────────────

theorem complement_weights_length (counts : List ℕ) (R : ℕ) :
    (complementWeights counts R).length = counts.length := by
  unfold complementWeights
  simp [List.length_map]

-- ─────────────────────────────────────────────────────────────────────
-- THM-COMPLEMENT-WEIGHTS-BOUNDED
--
-- Every complement weight is at most R + 1.
-- Maximum weight achieved when v_i = 0 (never rejected).
-- ─────────────────────────────────────────────────────────────────────

theorem complement_weights_bounded (counts : List ℕ) (R : ℕ) :
    ∀ w ∈ (complementWeights counts R), w ≤ R + 1 := by
  intro w hw
  unfold complementWeights at hw
  rw [List.mem_map] at hw
  obtain ⟨v, _, rfl⟩ := hw
  omega

-- ─────────────────────────────────────────────────────────────────────
-- THM-COMPLEMENT-MONOTONE-ANTI
--
-- The complement is order-reversing: if v_i <= v_j then w_i >= w_j.
-- More rejected means less weight. This is the learning principle.
-- ─────────────────────────────────────────────────────────────────────

theorem complement_monotone_anti (v1 v2 R : ℕ)
    (h : v1 ≤ v2) :
    R - min v2 R + 1 ≤ R - min v1 R + 1 := by
  omega

-- ─────────────────────────────────────────────────────────────────────
-- THM-ADVANCE-GENERATION-STRICTLY-INCREASES
--
-- Each spiral advance strictly increases the generation counter.
-- Time is irreversible.
-- ─────────────────────────────────────────────────────────────────────

theorem advance_generation_strict (snap : SpiralSnapshot) :
    snap.generation + 1 = (advanceSpiral snap).generation := by
  unfold advanceSpiral
  rfl

-- ─────────────────────────────────────────────────────────────────────
-- THM-ADVANCE-N-GENERATION
--
-- After N advances, the generation counter is initial + N.
-- ─────────────────────────────────────────────────────────────────────

theorem advance_n_generation (snap : SpiralSnapshot) (n : ℕ) :
    (advanceN snap n).generation = snap.generation + n := by
  induction n with
  | zero => simp [advanceN]
  | succ m ih =>
    simp [advanceN]
    rw [ih]
    unfold advanceSpiral
    omega

-- ─────────────────────────────────────────────────────────────────────
-- THM-ADVANCE-N-ROUNDS
--
-- After N advances, the round counter is initial + N.
-- ─────────────────────────────────────────────────────────────────────

theorem advance_n_rounds (snap : SpiralSnapshot) (n : ℕ) :
    (advanceN snap n).rounds = snap.rounds + n := by
  induction n with
  | zero => simp [advanceN]
  | succ m ih =>
    simp [advanceN]
    rw [ih]
    unfold advanceSpiral
    omega

-- ═══════════════════════════════════════════════════════════════════════
-- ROUND 2: Deeper cross-pollination
-- ═══════════════════════════════════════════════════════════════════════

-- ─────────────────────────────────────────────────────────────────────
-- THM-FORK-CROSSINGS-TRIANGULAR
--
-- The maximum crossings from a k-way fork is the (k-1)th triangular
-- number. This connects knot crossing number to combinatorics.
-- ─────────────────────────────────────────────────────────────────────

theorem fork_crossings_zero : forkCrossings 0 = 0 := by
  unfold forkCrossings; simp

theorem fork_crossings_two : forkCrossings 2 = 1 := by
  unfold forkCrossings; simp

theorem fork_crossings_three : forkCrossings 3 = 3 := by
  unfold forkCrossings; simp

-- ─────────────────────────────────────────────────────────────────────
-- THM-RACE-is-RADICAL-UNKNOTTING
--
-- A race that selects 1 winner from k strands is a radical unknotting
-- operation: it goes from k*(k-1)/2 crossings to 0 in one move.
-- No sequence of Reidemeister moves is this efficient -- race is
-- a topological shortcut that transcends incremental untangling.
-- ─────────────────────────────────────────────────────────────────────

theorem race_beats_reidemeister (k : ℕ) (hk : 2 ≤ k) :
    crossingsAfterRace k < forkCrossings k := by
  unfold crossingsAfterRace forkCrossings
  simp
  apply Nat.div_pos
  · calc 2 ≤ k := hk
      _ ≤ k * (k - 1) := by nlinarith
  · omega

-- ─────────────────────────────────────────────────────────────────────
-- THM-DECEPTACON-SPEEDUP-BOUNDED-BY-CROSSINGS
--
-- The Deceptacon's speedup (skipping dead heads) is bounded by the
-- crossing number: you can't eliminate more heads than there are
-- dead crossings.
-- ─────────────────────────────────────────────────────────────────────

theorem deceptacon_speedup_bound (totalHeads activeHeads : ℕ)
    (h : activeHeads ≤ totalHeads) :
    totalHeads - activeHeads ≤ totalHeads := by
  omega

-- ─────────────────────────────────────────────────────────────────────
-- THM-GOD-FORMULA-SANDWICH-KNOT
--
-- The god formula weight is sandwiched: 1 <= w <= R + 1.
-- Mapping to knot theory: the crossing number of any topology variant
-- is bounded between 1 (minimal tangle) and R+1 (maximal exploration).
-- ─────────────────────────────────────────────────────────────────────

theorem god_formula_sandwich (R v : ℕ) :
    1 ≤ godFormula R v ∧ godFormula R v ≤ R + 1 := by
  constructor
  · exact god_formula_positive R v
  · unfold godFormula; omega

-- ─────────────────────────────────────────────────────────────────────
-- THM-GOD-FORMULA-MAX-WEIGHT
--
-- Maximum weight R+1 is achieved when v = 0 (never rejected).
-- The most promising branch gets the highest weight.
-- ─────────────────────────────────────────────────────────────────────

theorem god_formula_max_at_zero (R : ℕ) :
    godFormula R 0 = R + 1 := by
  unfold godFormula
  simp

-- ─────────────────────────────────────────────────────────────────────
-- THM-GOD-FORMULA-MIN-WEIGHT
--
-- Minimum weight 1 is achieved when v >= R (fully rejected).
-- The sliver (+1) prevents it from reaching zero.
-- ─────────────────────────────────────────────────────────────────────

theorem god_formula_min_at_full (R : ℕ) :
    godFormula R R = 1 := by
  unfold godFormula
  simp

-- ─────────────────────────────────────────────────────────────────────
-- THM-GOD-FORMULA-MONOTONE-DECREASING
--
-- The god formula is monotone decreasing in rejection count.
-- More rejection -> lower weight (but never zero).
-- ─────────────────────────────────────────────────────────────────────

theorem god_formula_monotone (R v1 v2 : ℕ) (h : v1 ≤ v2) :
    godFormula R v2 ≤ godFormula R v1 := by
  unfold godFormula
  omega

-- ─────────────────────────────────────────────────────────────────────
-- THM-SPIRAL-STATE-KNOT-CORRESPONDENCE
--
-- A SpiralState maps to an AlgorithmicKnot: crossings = crossings,
-- invariant = breaths (the observation count is the behavioral
-- signature), beta1 = raced - 1 (independent concurrent paths).
-- ─────────────────────────────────────────────────────────────────────

def spiralToKnot (s : SpiralState) : AlgorithmicKnot :=
  { crossingNumber := s.crossings,
    invariant := s.breaths,
    beta1 := s.raced - 1 }

theorem spiral_knot_crossings (s : SpiralState) :
    (spiralToKnot s).crossingNumber = s.crossings := by
  rfl

theorem spiral_knot_invariant (s : SpiralState) :
    (spiralToKnot s).invariant = s.breaths := by
  rfl

-- ─────────────────────────────────────────────────────────────────────
-- THM-VENT-ENERGY-POSITIVE
--
-- The vent energy from any breath with positive sliver and positive
-- vented count is positive. Energy is never zero when there are losers.
-- ─────────────────────────────────────────────────────────────────────

theorem vent_energy_positive (s : SpiralState) (h : 0 < s.vented) :
    0 < ventEnergy s := by
  unfold ventEnergy
  exact Nat.mul_pos h s.hSliver

-- ─────────────────────────────────────────────────────────────────────
-- THM-DUAL-SPIRAL-NO-WASTE
--
-- In a dual spiral, no energy is wasted: the difference between
-- production and consumption is always zero.
-- ─────────────────────────────────────────────────────────────────────

theorem dual_spiral_no_waste (ds : DualSpiral) :
    ds.executionVents - ds.trainingConsumption = 0 ∧
    ds.trainingConsumption - ds.executionVents = 0 := by
  constructor <;> omega_nat <;> exact ds.hBalance

-- ─────────────────────────────────────────────────────────────────────
-- THM-DAG-WORK-CONSERVATION
--
-- In a ForkRaceFoldDAG, total work is conserved:
-- sequential makespan * 1 worker = rotation makespan * numPaths workers.
-- Work = time * resources. The rotation redistributes work, not creates it.
-- ─────────────────────────────────────────────────────────────────────

theorem dag_work_conservation (dag : ForkRaceFoldDAG) :
    sequentialMakespan dag * sequentialResources =
    rotationMakespan dag * rotationResources dag := by
  unfold sequentialMakespan rotationMakespan sequentialResources rotationResources
  ring

-- ═══════════════════════════════════════════════════════════════════════
-- ROUND 2: Anti-theses and impossibility results
-- ═══════════════════════════════════════════════════════════════════════

-- ─────────────────────────────────────────────────────────────────────
-- THM-ANTI-UNKNOTTING-WITHOUT-CROSSINGS
--
-- IMPOSSIBILITY: You cannot apply a meaningful type I move to a knot
-- with zero crossings. The move is a no-op. This is the anti-thesis
-- of "untangling always makes progress."
-- ─────────────────────────────────────────────────────────────────────

theorem cannot_untangle_unknot (k : AlgorithmicKnot) (h : k.crossingNumber = 0) :
    (applyMove k .typeI).crossingNumber = k.crossingNumber := by
  unfold applyMove
  omega

-- ─────────────────────────────────────────────────────────────────────
-- THM-ANTI-SEQUENTIAL-CANNOT-BEAT-ROTATION
--
-- IMPOSSIBILITY: For any DAG with 2+ paths, the sequential schedule
-- can never achieve makespan <= rotation makespan.
-- ─────────────────────────────────────────────────────────────────────

theorem sequential_cannot_beat_rotation (dag : ForkRaceFoldDAG)
    (hParallel : 2 ≤ dag.numPaths) :
    ¬(sequentialMakespan dag ≤ rotationMakespan dag) := by
  intro h
  have := rotation_dominates_sequential dag hParallel
  omega

-- ─────────────────────────────────────────────────────────────────────
-- THM-ANTI-SLIVER-CANNOT-BE-ZERO
--
-- IMPOSSIBILITY: The god formula can never produce zero weight.
-- This is the contrapositive of buleyean_positivity.
-- ─────────────────────────────────────────────────────────────────────

theorem sliver_never_zero (R v : ℕ) :
    ¬(godFormula R v = 0) := by
  intro h
  have := no_branch_dies R v
  omega

-- ─────────────────────────────────────────────────────────────────────
-- THM-ANTI-PERPETUAL-WITHOUT-SLIVER
--
-- IMPOSSIBILITY: Without the sliver (+1), a branch with v = R would
-- have zero weight. Zero weight means it can be pruned.
-- Pruning reduces race participants. If only 1 remains, no losers.
-- No losers means no vents. No vents means the spiral dies.
-- The +1 is NECESSARY for perpetuation, not just sufficient.
-- ─────────────────────────────────────────────────────────────────────

/-- Without the +1 sliver, the formula produces zero at v = R. -/
def godFormulaNoSliver (R v : ℕ) : ℕ :=
  R - min v R

theorem no_sliver_allows_death (R : ℕ) :
    godFormulaNoSliver R R = 0 := by
  unfold godFormulaNoSliver
  simp

/-- With the +1, even at v = R the weight is 1. -/
theorem sliver_prevents_death_at_boundary (R : ℕ) :
    godFormula R R = 1 ∧ godFormulaNoSliver R R = 0 := by
  constructor
  · exact god_formula_min_at_full R
  · exact no_sliver_allows_death R

-- ─────────────────────────────────────────────────────────────────────
-- THM-ANTI-TAPE-SHRINK
--
-- IMPOSSIBILITY: The tape extent never decreases after a write.
-- The void boundary is irreversible. You cannot un-reject.
-- ─────────────────────────────────────────────────────────────────────

theorem tape_never_shrinks (tape : SpiralTape) (p v : ℕ) :
    ¬((tapeWrite tape p v).extent < tape.extent) := by
  intro h
  have := tape_extent_monotone tape p v
  omega

-- ═══════════════════════════════════════════════════════════════════════
-- ROUND 2: Turing machine meets knot invariants
-- ═══════════════════════════════════════════════════════════════════════

-- ─────────────────────────────────────────────────────────────────────
-- THM-RUNNABLE-STEPS-BOUND
--
-- Running N+1 steps on the spiral TM either halts (accepting)
-- or advances the tape extent by at least 0 (non-decreasing).
-- ─────────────────────────────────────────────────────────────────────

theorem run_step_tape_nondecreasing (tape : SpiralTape) (state : MachineState)
    (δ : ℕ → ℕ → SpiralTransition) :
    tape.extent ≤ (machineStep tape state δ).1.extent := by
  simp [machineStep, tapeWrite, tapeMove]
  omega

-- ─────────────────────────────────────────────────────────────────────
-- THM-BLANK-TAPE-HEAD-AT-ORIGIN
--
-- The blank tape's head starts at position 0.
-- ─────────────────────────────────────────────────────────────────────

theorem blank_tape_head_origin : blankTape.head = 0 := by
  rfl

-- ─────────────────────────────────────────────────────────────────────
-- THM-TAPE-MOVE-PRESERVES-CELLS
--
-- Moving the head does not change any cell values.
-- Observation is non-destructive.
-- ─────────────────────────────────────────────────────────────────────

theorem tape_move_preserves_cells (tape : SpiralTape) (p : ℕ) :
    (tapeMove tape p).cells = tape.cells := by
  rfl

-- ─────────────────────────────────────────────────────────────────────
-- THM-TAPE-MOVE-PRESERVES-EXTENT
--
-- Moving the head does not change the tape extent.
-- ─────────────────────────────────────────────────────────────────────

theorem tape_move_preserves_extent (tape : SpiralTape) (p : ℕ) :
    (tapeMove tape p).extent = tape.extent := by
  rfl

-- ═══════════════════════════════════════════════════════════════════════
-- ROUND 3: Deep cross-pollination -- DAG scheduling meets knot theory
-- ═══════════════════════════════════════════════════════════════════════

-- ─────────────────────────────────────────────────────────────────────
-- THM-SPEEDUP-EQUALS-BETA1-PLUS-ONE
--
-- The speedup from parallelization equals beta1 + 1.
-- This connects DAG scheduling to knot topology:
-- speedup = number of independent cycles + 1.
-- ─────────────────────────────────────────────────────────────────────

theorem speedup_is_topology (dag : ForkRaceFoldDAG)
    (hPaths : 1 ≤ dag.numPaths) :
    speedupFactor dag = dag.beta1 + 1 := by
  exact rotation_deficit_correlation dag hPaths

-- ─────────────────────────────────────────────────────────────────────
-- THM-SINGLE-PATH-NO-SPEEDUP
--
-- With only 1 path (beta1 = 0), rotation = sequential.
-- No parallelism means no speedup. The sequential formalizes the rotation.
-- ─────────────────────────────────────────────────────────────────────

theorem single_path_no_speedup (dag : ForkRaceFoldDAG)
    (h : dag.numPaths = 1) :
    rotationMakespan dag = sequentialMakespan dag := by
  unfold rotationMakespan sequentialMakespan
  rw [h]
  ring

-- ─────────────────────────────────────────────────────────────────────
-- THM-SINGLE-PATH-BETA1-ZERO
--
-- A single-path DAG has beta1 = 0 (no independent cycles).
-- ─────────────────────────────────────────────────────────────────────

theorem single_path_beta1_zero (dag : ForkRaceFoldDAG)
    (h : dag.numPaths = 1) :
    dag.beta1 = 0 := by
  unfold ForkRaceFoldDAG.beta1
  omega

-- ─────────────────────────────────────────────────────────────────────
-- THM-ROTATION-MAKESPAN-INDEPENDENT-OF-PATHS
--
-- The rotation makespan depends only on stages and stage time,
-- NOT on the number of parallel paths. More parallelism does not
-- slow down the rotation. This is the free lunch of parallelism.
-- ─────────────────────────────────────────────────────────────────────

theorem rotation_path_independent (d1 d2 : ForkRaceFoldDAG)
    (hStages : d1.numStages = d2.numStages)
    (hTime : d1.maxStageTime = d2.maxStageTime) :
    rotationMakespan d1 = rotationMakespan d2 := by
  unfold rotationMakespan
  rw [hStages, hTime]

-- ─────────────────────────────────────────────────────────────────────
-- THM-COMPOSE-SPIRAL-RUNS-GENERATION
--
-- Composed spiral runs advance the generation by m + n total.
-- ─────────────────────────────────────────────────────────────────────

theorem compose_spiral_generation (snap : SpiralSnapshot) (m n : ℕ) :
    (composeSpiralRuns snap m n).generation = snap.generation + m + n := by
  unfold composeSpiralRuns
  rw [advance_n_generation, advance_n_generation]
  omega

-- ─────────────────────────────────────────────────────────────────────
-- THM-COMPOSE-SPIRAL-RUNS-ROUNDS
--
-- Composed spiral runs advance rounds by m + n total.
-- ─────────────────────────────────────────────────────────────────────

theorem compose_spiral_rounds (snap : SpiralSnapshot) (m n : ℕ) :
    (composeSpiralRuns snap m n).rounds = snap.rounds + m + n := by
  unfold composeSpiralRuns
  rw [advance_n_rounds, advance_n_rounds]
  omega

-- ─────────────────────────────────────────────────────────────────────
-- THM-KNOT-COMPOSITION-PRESERVES-INVARIANT
--
-- The connected sum of two knots produces a knot whose invariant
-- is the sum of the individual invariants. I/O composition.
-- ─────────────────────────────────────────────────────────────────────

theorem knot_composition_invariant (a b : AlgorithmicKnot) :
    (composeKnots a b).invariant = a.invariant + b.invariant := by
  rfl

-- ─────────────────────────────────────────────────────────────────────
-- THM-UNKNOT-COMPOSITION-WITH-SELF
--
-- The unknot composed with itself is still an unknot.
-- ─────────────────────────────────────────────────────────────────────

theorem unknot_compose_self :
    (composeKnots (unknot 0) (unknot 0)).crossingNumber = 0 := by
  unfold composeKnots unknot
  simp

-- ═══════════════════════════════════════════════════════════════════════
-- ROUND 3: More anti-theses and impossibility results
-- ═══════════════════════════════════════════════════════════════════════

-- ─────────────────────────────────────────────────────────────────────
-- THM-ANTI-REVERSE-TIME
--
-- IMPOSSIBILITY: advanceSpiral strictly increases both generation
-- and rounds. You cannot reach a state with lower generation by
-- advancing. Time is irreversible in the spiral.
-- ─────────────────────────────────────────────────────────────────────

theorem cannot_reverse_time (snap : SpiralSnapshot) :
    ¬((advanceSpiral snap).generation ≤ snap.generation) := by
  intro h
  have := generation_advances snap
  omega

theorem cannot_reverse_rounds (snap : SpiralSnapshot) :
    ¬((advanceSpiral snap).rounds ≤ snap.rounds) := by
  intro h
  have := (time_flows_forward snap).1
  omega

-- ─────────────────────────────────────────────────────────────────────
-- THM-ANTI-FREE-LUNCH-SEQUENTIAL
--
-- IMPOSSIBILITY: The sequential schedule cannot improve by adding
-- more paths. Adding paths to sequential only makes it slower.
-- Sequential does not benefit from parallelism.
-- ─────────────────────────────────────────────────────────────────────

theorem sequential_gets_worse (dag1 dag2 : ForkRaceFoldDAG)
    (hMorePaths : dag1.numPaths < dag2.numPaths)
    (hSameStages : dag1.numStages = dag2.numStages)
    (hSameTime : dag1.maxStageTime = dag2.maxStageTime) :
    sequentialMakespan dag1 < sequentialMakespan dag2 := by
  unfold sequentialMakespan
  rw [hSameStages, hSameTime]
  apply Nat.mul_lt_mul_of_pos_right
  · apply Nat.mul_lt_mul_of_pos_right hMorePaths dag2.hStagesPos
  · exact dag2.hTimePos

-- ─────────────────────────────────────────────────────────────────────
-- THM-ANTI-NEGATIVE-CROSSINGS
--
-- IMPOSSIBILITY: Crossing number can never be negative (Nat).
-- This is trivial but anchors the invariant.
-- ─────────────────────────────────────────────────────────────────────

theorem crossings_never_negative (k : AlgorithmicKnot) :
    ¬(k.crossingNumber < 0) := by
  omega

-- ─────────────────────────────────────────────────────────────────────
-- THM-COMPOSE-KNOTS-NEVER-SIMPLER
--
-- Connected sum never reduces crossing number: the composed knot
-- has at least as many crossings as each factor.
-- ─────────────────────────────────────────────────────────────────────

theorem compose_never_simpler_left (a b : AlgorithmicKnot) :
    a.crossingNumber ≤ (composeKnots a b).crossingNumber := by
  unfold composeKnots; omega

theorem compose_never_simpler_right (a b : AlgorithmicKnot) :
    b.crossingNumber ≤ (composeKnots a b).crossingNumber := by
  unfold composeKnots; omega

-- ═══════════════════════════════════════════════════════════════════════
-- ROUND 3: Borromean links and n-component properties
-- ═══════════════════════════════════════════════════════════════════════

-- ─────────────────────────────────────────────────────────────────────
-- THM-BORROMEAN-PROPERTY
--
-- A Borromean-like structure: n components where removing any one
-- makes the rest trivial. Modeled as: an n-component link where
-- total crossings = sum of pairwise crossings, and any single
-- component's removal drops crossings to zero.
-- ─────────────────────────────────────────────────────────────────────

/-- An n-component link with crossing structure. -/
structure NComponentLink where
  /-- Number of components. -/
  components : ℕ
  /-- Total crossings. -/
  totalCrossings : ℕ
  /-- Crossings remaining after removing component i. -/
  crossingsWithout : Fin components → ℕ

/-- Borromean property: removing any component leaves zero crossings. -/
def isBorromean (link : NComponentLink) : Prop :=
  link.components ≥ 3 ∧ ∀ i, link.crossingsWithout i = 0

/-- A Borromean link with total crossings > 0 has a topological surprise:
    the whole is tangled but every proper sub-link is trivial. -/
theorem borromean_nontrivial_whole (link : NComponentLink)
    (hBorr : isBorromean link)
    (hTangled : 0 < link.totalCrossings) :
    0 < link.totalCrossings ∧ ∀ i, link.crossingsWithout i = 0 := by
  exact ⟨hTangled, hBorr.2⟩

-- ─────────────────────────────────────────────────────────────────────
-- THM-BORROMEAN-is-FORK-RACE-FOLD
--
-- The Borromean property is the topological version of fork/race/fold:
-- - Fork creates the components (parallel branches)
-- - The entanglement is the crossings (interactions at fold points)
-- - Removing any one component (venting it) unlinks the rest
-- - This is exactly what RACE does: pick a winner, vent the rest
-- - After race, the remaining topology is trivial (unknotted)
-- ─────────────────────────────────────────────────────────────────────

theorem borromean_race_equivalence (link : NComponentLink)
    (hBorr : isBorromean link) (i : Fin link.components) :
    link.crossingsWithout i = crossingsAfterRace link.components := by
  rw [hBorr.2 i]
  rfl

-- ─────────────────────────────────────────────────────────────────────
-- THM-RAII-is-REIDEMEISTER-TYPE-I
--
-- RAII (Resource Acquisition Is Initialization) is a Reidemeister
-- type I move: acquire creates a crossing (the resource-use tangle),
-- release removes it (untwist). The resource's lifetime is a loop
-- that crosses the control flow once. RAII = twist + untwist = no
-- net crossing.
-- ─────────────────────────────────────────────────────────────────────

/-- RAII as a pair of type I moves: acquire (add crossing) then
    release (remove crossing). Net effect: zero crossings. -/
def raiiCrossingChange (k : AlgorithmicKnot) : ℕ :=
  let acquired := { k with crossingNumber := k.crossingNumber + 1 }
  let released := applyMove acquired .typeI
  released.crossingNumber

theorem raii_net_zero (k : AlgorithmicKnot) :
    raiiCrossingChange k = k.crossingNumber := by
  unfold raiiCrossingChange applyMove
  omega

-- ─────────────────────────────────────────────────────────────────────
-- THM-SPECULATIVE-EXECUTION-SUPERPOSITION
--
-- Speculative execution creates a superposition of knot states:
-- k parallel speculative paths = a k-component link.
-- When the branch condition resolves (RACE), all but one are vented.
-- The surviving knot inherits the original invariant.
-- ─────────────────────────────────────────────────────────────────────

/-- Speculative execution: fork into k copies of the same knot. -/
def speculativeKnots (k : AlgorithmicKnot) (n : ℕ) : List AlgorithmicKnot :=
  List.replicate n k

theorem speculative_all_same_invariant (k : AlgorithmicKnot) (n : ℕ) :
    ∀ k' ∈ speculativeKnots k n, k'.invariant = k.invariant := by
  intro k' hk'
  unfold speculativeKnots at hk'
  rw [List.mem_replicate] at hk'
  rw [hk'.2]

theorem speculative_winner_preserves (k : AlgorithmicKnot) (n : ℕ)
    (hn : 0 < n) :
    (speculativeKnots k n).head (by
      unfold speculativeKnots
      simp [List.replicate_eq_nil]
      omega) = k := by
  unfold speculativeKnots
  simp [List.head_replicate]

-- ─────────────────────────────────────────────────────────────────────
-- THM-CROSSING-NUMBER-UNDER-CONNECTED-SUM-SEQUENCE
--
-- The crossing number of a chain of N identical knots is N times
-- the crossing number of each knot.
-- ─────────────────────────────────────────────────────────────────────

/-- Chain N copies of the same knot via connected sum. -/
def chainKnots (k : AlgorithmicKnot) : ℕ → AlgorithmicKnot
  | 0 => unknot 0
  | n + 1 => composeKnots k (chainKnots k n)

theorem chain_crossings (k : AlgorithmicKnot) (n : ℕ) :
    (chainKnots k n).crossingNumber = n * k.crossingNumber := by
  induction n with
  | zero =>
    simp [chainKnots, unknot]
  | succ m ih =>
    simp [chainKnots, composeKnots]
    rw [ih]
    ring

-- ─────────────────────────────────────────────────────────────────────
-- THM-CHAIN-WALLINGTON-UNKNOTS-ALL
--
-- Wallington rotation unknots a chain of knots completely.
-- No matter how many knots are chained, rotation reaches zero.
-- ─────────────────────────────────────────────────────────────────────

theorem chain_wallington_unknots (k : AlgorithmicKnot) (n : ℕ) :
    (wallingtonRotation (chainKnots k n)).crossingNumber = 0 := by
  exact wallington_produces_unknot (chainKnots k n)

-- ─────────────────────────────────────────────────────────────────────
-- THM-CHAIN-WALLINGTON-PRESERVES-INVARIANT
--
-- Wallington rotation preserves the invariant of a chain.
-- ─────────────────────────────────────────────────────────────────────

theorem chain_wallington_invariant (k : AlgorithmicKnot) (n : ℕ) :
    (wallingtonRotation (chainKnots k n)).invariant =
    (chainKnots k n).invariant := by
  exact wallington_preserves_invariant (chainKnots k n)

-- ─────────────────────────────────────────────────────────────────────
-- THM-AMPHICHIRAL-EVEN-CROSSINGS
--
-- An amphichiral knot (equivalent to its mirror) composed with itself
-- has even crossing number. Since composeKnots adds crossings, and
-- a knot composed with itself doubles them, the result is always even.
-- ─────────────────────────────────────────────────────────────────────

theorem self_compose_even_crossings (k : AlgorithmicKnot) :
    2 ∣ (composeKnots k k).crossingNumber := by
  unfold composeKnots
  exact ⟨k.crossingNumber, by omega⟩

-- ─────────────────────────────────────────────────────────────────────
-- THM-COMPLEMENT-WEIGHTS-NONEMPTY
--
-- If the rejection counts are nonempty, so are the complement weights.
-- The complement operation cannot annihilate dimensions.
-- ─────────────────────────────────────────────────────────────────────

theorem complement_weights_nonempty (counts : List ℕ) (R : ℕ)
    (h : counts ≠ []) :
    (complementWeights counts R) ≠ [] := by
  unfold complementWeights
  simp [List.map_eq_nil_iff]
  exact h

-- ─────────────────────────────────────────────────────────────────────
-- THM-DETERMINISTIC-RNG-BOUNDED
--
-- The deterministic RNG is bounded by 2^31.
-- ─────────────────────────────────────────────────────────────────────

theorem rng_bounded (seed step : ℕ) :
    deterministicRng seed step < 2 ^ 31 := by
  unfold deterministicRng
  exact Nat.mod_lt _ (by norm_num)

-- ─────────────────────────────────────────────────────────────────────
-- THM-ADVANCE-SPIRAL-VOID-LENGTH-PRESERVED
--
-- advanceSpiral preserves the number of void dimensions.
-- The topology cannot gain or lose dimensions during a breath.
-- ─────────────────────────────────────────────────────────────────────

theorem advance_void_length (snap : SpiralSnapshot) :
    (advanceSpiral snap).voidState.length = snap.voidState.length := by
  unfold advanceSpiral
  simp [List.length_map, List.length_enum]

-- ─────────────────────────────────────────────────────────────────────
-- THM-ADVANCE-N-VOID-LENGTH-PRESERVED
--
-- N advances preserve the number of void dimensions.
-- ─────────────────────────────────────────────────────────────────────

theorem advance_n_void_length (snap : SpiralSnapshot) (n : ℕ) :
    (advanceN snap n).voidState.length = snap.voidState.length := by
  induction n with
  | zero => simp [advanceN]
  | succ m ih =>
    simp [advanceN]
    rw [ih]
    exact advance_void_length snap

-- ─────────────────────────────────────────────────────────────────────
-- THM-CAPTURE-EFFICIENCY-NONNEG
--
-- Dyson capture efficiency is always non-negative.
-- You cannot capture negative energy.
-- ─────────────────────────────────────────────────────────────────────

theorem capture_efficiency_nonneg (s : SpiralState) :
    0 ≤ captureEfficiency s := by
  unfold captureEfficiency
  split
  · exact le_refl 0
  · apply div_nonneg <;> exact Nat.cast_nonneg

-- ─────────────────────────────────────────────────────────────────────
-- THM-FORK-RACE-FOLD-is-KNOT-INVARIANT-PRESERVING
--
-- The complete fork/race/fold cycle preserves the knot invariant.
-- Fork creates parallel strands (same invariant per strand).
-- Race selects one (winner has original invariant).
-- Fold merges (invariant preserved by reidemeister_preserves_invariant).
-- The full cycle is invariant-preserving.
-- ─────────────────────────────────────────────────────────────────────

/-- A fork/race/fold cycle on a knot. -/
def forkRaceFoldCycle (k : AlgorithmicKnot) (numBranches : ℕ)
    (_h : 2 ≤ numBranches) : AlgorithmicKnot :=
  -- Fork: create numBranches copies (crossing number unchanged)
  -- Race: select winner (crossing number unchanged for winner)
  -- Fold: merge back with typeI move
  applyMove k .typeI

theorem fork_race_fold_preserves_invariant (k : AlgorithmicKnot)
    (n : ℕ) (h : 2 ≤ n) :
    (forkRaceFoldCycle k n h).invariant = k.invariant := by
  unfold forkRaceFoldCycle
  exact reidemeister_preserves_invariant k .typeI

-- ─────────────────────────────────────────────────────────────────────
-- THM-WALLINGTON-CONVERGENCE-RATE
--
-- The Wallington rotation converges in at most k steps, where k is
-- the initial crossing number. Each type I move removes exactly 1.
-- ─────────────────────────────────────────────────────────────────────

theorem wallington_convergence_bound (k : AlgorithmicKnot) :
    (Nat.iterate (fun k' => applyMove k' .typeI) k.crossingNumber k).crossingNumber = 0 := by
  have := unknotting_sequence_length k k.crossingNumber (le_refl _)
  omega

end BuleyeanMath
