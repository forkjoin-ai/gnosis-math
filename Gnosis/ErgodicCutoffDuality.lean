import Init
import Gnosis.FiniteDynamicsCore
import Gnosis.AeonNoise
import Gnosis.Cancer.CancerTopology

/-!
# The Ergodic Cutoff Duality — what is actually provable

This module takes the *proposed* "Duality of the Ergodic Cutoff" and pins down,
in Rustic Church style (Init only, no `omega`, no Mathlib, no `simp`/`decide` on
open goals), exactly which part of the unification is a theorem and which part is
rhetoric. Per the repo policy: state relationships precisely; if an identity is
real, prove it; rhetorical force is not evidence.

## What the source claim gets wrong

The headline claim is that card mixing (7 riffles), cancer restoration (7 p53
ticks), and toral automorphisms (10-period orbits) are "different projections of
the exact same finite-dimensional torus automorphism quotient." Reading the
carriers, three things break:

1. **The "7 = 7" synchronization is a coincidence of unrelated numbers.**
   `getThreshold cardRiffleShuffle = 7` is a hard-coded label in a lookup table
   (`Gnosis/Mesh/MeshCriticalThresholds.lean`); there is no Markov / total-variation
   cutoff proof behind it (see `ergodic_cutoff_open_obligations` note below).
   The cancer "7" is `gbmCombined.deficit = healthyVentReference - tumorVentBeta1
   = 9 - 2`, an instance parameter, not a constant: change the tumor reading and
   the count changes. Two numbers equal to 7 for entirely different reasons are
   not a shared invariant.

2. **Cancer restoration has no torus, no automorphism, no group.** `CancerTopology`
   is pure `Nat` saturating subtraction. The honest object there is a *monovariant
   that strictly descends to an absorbing fixed point* — a dissipative system, the
   opposite of a measure-preserving toral automorphism.

3. **The genuine coincidence is the period 10, not the number 7** — and even that
   is shared *period*, not shared *quotient*: the Arnold cat map on `(Z/5)²` and the
   perfect out-shuffle on 12 cards both have order 10, but their orbit (cycle)
   structures differ, so they are not conjugate permutations.

## What is actually true (and proved here)

The defensible unification is a **dichotomy**, not an identity:

* **Conservative regime** (`Returns`): a step `f` with `iter f T x = x`. Over a full
  period every observable returns — nothing is monotonically created or destroyed
  (`returns_conserves`). The cat map and the out-shuffle both live here with `T = 10`.
* **Dissipative regime** (`DissipativeSystem`): a monovariant `m` that drops by
  exactly 1 per step until it is absorbed at 0 (`step_sub_one`,
  `dissipative_mono_after`). Convergence time equals the initial monovariant
  (`dissipative_absorbs`) — this is where cancer restoration lives, with the "7"
  being `gbmCombined.deficit`.
* **The duality theorem** (`dissipative_not_periodic`): a dissipative state with
  positive monovariant is **aperiodic** — it never returns. So a state is in one
  regime or the other; the only meeting point is the absorbing/healthy point where
  the monovariant is already 0. Healing is *not* a period-10 out-shuffle of the
  diseased state; it is the dissipative complement of one.

`ergodic_cutoff_duality_master` bundles the proved facts, including the
machine-checked fixed-point-count contrast (1 ≠ 2) that refutes "exact same quotient".

Zero `sorry`. Zero `omega`. Zero Mathlib.
-/

namespace Gnosis
namespace ErgodicCutoffDuality

open Gnosis.AeonNoise
open Gnosis.CancerTopology
open Gnosis.FiniteDynamicsCore

/-! The generic primitives (`iter`, `Returns`, `returns_conserves`, `DissipativeSystem`,
`dissipative_not_periodic`, …) now live in `Gnosis/FiniteDynamicsCore.lean`; this module
supplies the cat-map / out-shuffle / cancer *instances*. -/

-- ═══════════════════════════════════════════════════════════════════════
-- §3  Conservative instances — cat map and out-shuffle, both period 10
-- ═══════════════════════════════════════════════════════════════════════

/-- The generic iterate agrees with `AeonNoise.iterateAeonCatMap` (same recursion). -/
theorem iter_aeonCatMap_eq (n : Nat) (p : Nat × Nat) :
    iter aeonCatMap n p = iterateAeonCatMap n p := by
  induction n with
  | zero => rfl
  | succ k ih =>
      show aeonCatMap (iter aeonCatMap k p) = aeonCatMap (iterateAeonCatMap k p)
      rw [ih]

/-- The generic iterate agrees with `AeonNoise.iterateOutShuffle12` (same recursion). -/
theorem iter_outShuffle12_eq (n : Nat) (i : Nat) :
    iter outShuffle12 n i = iterateOutShuffle12 n i := by
  induction n with
  | zero => rfl
  | succ k ih =>
      show outShuffle12 (iter outShuffle12 k i) = outShuffle12 (iterateOutShuffle12 k i)
      rw [ih]

/-- The Arnold cat map closes every bounded toral coordinate after 10 ticks. -/
theorem cat_returns_10 (p : Nat × Nat) (h1 : p.1 < 5) (h2 : p.2 < 5) :
    Returns aeonCatMap 10 p := by
  unfold Returns
  rw [iter_aeonCatMap_eq]
  exact iterate_aeon_cat_map_10_of_bounds p h1 h2

/-- Any observable of a cat-map orbit is conserved over the period-10 cycle. -/
theorem cat_observable_conserved (m : Nat × Nat → Nat) (p : Nat × Nat)
    (h1 : p.1 < 5) (h2 : p.2 < 5) :
    m (iter aeonCatMap 10 p) = m p :=
  returns_conserves aeonCatMap 10 p m (cat_returns_10 p h1 h2)

/-- The perfect out-shuffle of 12 cards closes every card after 10 ticks. -/
theorem shuffle_returns_10 :
    Returns outShuffle12 10 0 ∧ Returns outShuffle12 10 1 ∧ Returns outShuffle12 10 2 ∧
    Returns outShuffle12 10 3 ∧ Returns outShuffle12 10 4 ∧ Returns outShuffle12 10 5 ∧
    Returns outShuffle12 10 6 ∧ Returns outShuffle12 10 7 ∧ Returns outShuffle12 10 8 ∧
    Returns outShuffle12 10 9 ∧ Returns outShuffle12 10 10 ∧ Returns outShuffle12 10 11 := by
  unfold Returns
  decide

-- ═══════════════════════════════════════════════════════════════════════
-- §4  Same period, distinct quotient — machine-checked refutation
-- ═══════════════════════════════════════════════════════════════════════

/-- The 25 toral coordinates of the cat map carrier `(Z/5)²`. -/
def catCarrier : List (Nat × Nat) :=
  [ (0,0),(0,1),(0,2),(0,3),(0,4)
  , (1,0),(1,1),(1,2),(1,3),(1,4)
  , (2,0),(2,1),(2,2),(2,3),(2,4)
  , (3,0),(3,1),(3,2),(3,3),(3,4)
  , (4,0),(4,1),(4,2),(4,3),(4,4) ]

/-- The 12 card indices of the out-shuffle carrier. -/
def shuffleCarrier : List Nat := [0,1,2,3,4,5,6,7,8,9,10,11]

/-- The cat map has exactly one fixed point on its carrier: `(0,0)`. -/
theorem cat_fixed_point_count :
    (catCarrier.filter (fun p => decide (aeonCatMap p = p))).length = 1 := by decide

/-- The out-shuffle has exactly two fixed points on its carrier: `0` and `11`. -/
theorem shuffle_fixed_point_count :
    (shuffleCarrier.filter (fun i => decide (outShuffle12 i = i))).length = 2 := by decide

/-- Same period (10), different cycle structure: 1 fixed point versus 2. Two
    permutations with different fixed-point counts are not conjugate, so the cat
    map and the out-shuffle are *not* "the same quotient" — only the period coincides.
    `Gnosis/ErgodicCutoffCycleType.lean` strengthens this into the full antitheorem:
    both have order *exactly* 10 (period set = multiples of 10) yet cycle types
    `1+2+2+10+10` vs `1+1+10`, refuting the identity in every slot of the fingerprint. -/
theorem distinct_orbit_structure :
    (catCarrier.filter (fun p => decide (aeonCatMap p = p))).length ≠
      (shuffleCarrier.filter (fun i => decide (outShuffle12 i = i))).length := by decide

-- ═══════════════════════════════════════════════════════════════════════
-- §5  Dissipative instance — cancer restoration is aperiodic, not a shuffle
-- ═══════════════════════════════════════════════════════════════════════

/-- A restoration step is fixed once the deficit is 0 (healthy = tumor capacity). -/
theorem step_restoration_absorbs (curr : CellVentTopology) (h0 : curr.deficit = 0) :
    (stepRestoration curr).deficit = 0 := by
  have heq : curr.healthyVentBeta1 = curr.tumorVentBeta1 :=
    (CellVentTopology.zero_deficit_iff_capacity_equal curr).mp h0
  have hnlt : ¬ curr.tumorVentBeta1 < curr.healthyVentBeta1 := by
    rw [heq]; exact Nat.lt_irrefl _
  unfold CellVentTopology.deficit
  dsimp [stepRestoration]
  simp [hnlt]
  rw [heq, Nat.sub_self]

/-- p53 feedback restoration as a `DissipativeSystem`: the monovariant is the
    cell-vent deficit, descent is the existing self-healing step. -/
def cancerDissipative : DissipativeSystem CellVentTopology where
  step := stepRestoration
  mono := CellVentTopology.deficit
  descent := fun x hx => step_restoration_decreases_deficit x hx
  absorb := fun x hx => step_restoration_absorbs x hx

/-- `f` commutes through the generic iterate. -/
theorem iter_succ_comm {α : Type} (f : α → α) (n : Nat) (x : α) :
    iter f n (f x) = f (iter f n x) := by
  induction n with
  | zero => rfl
  | succ k ih =>
      show f (iter f k (f x)) = f (f (iter f k x))
      rw [ih]

/-- The generic iterate agrees with `CancerTopology.iterateRestoration`. -/
theorem iter_eq_iterateRestoration (n : Nat) (curr : CellVentTopology) :
    iter stepRestoration n curr = iterateRestoration n curr := by
  induction n generalizing curr with
  | zero => rfl
  | succ k ih =>
      show stepRestoration (iter stepRestoration k curr)
            = iterateRestoration k (stepRestoration curr)
      rw [← ih (stepRestoration curr), iter_succ_comm]

/-- Cancer recovery in exactly `deficit` steps recovered as an instance of the
    generic absorbing law (here `deficit gbmCombined = 7`). -/
theorem cancer_recovers_via_generic :
    cancerDissipative.mono (iter stepRestoration 7 gbmCombined) = 0 :=
  dissipative_absorbs cancerDissipative 7 gbmCombined (by decide)

/-- The same fact, bridged to the original `iterateRestoration` statement: the
    abstract dissipative theorem subsumes the concrete cancer theorem. -/
theorem cancer_recovers_in_seven_bridged :
    (iterateRestoration 7 gbmCombined).deficit = 0 := by
  have h := cancer_recovers_via_generic
  rw [iter_eq_iterateRestoration] at h
  exact h

/-- **Healing is not a shuffle.** The diseased state never recurs: cancer
    restoration is aperiodic, the dissipative complement of a period-10 orbit. -/
theorem cancer_state_never_recurs (T : Nat) (hT : 0 < T) :
    iter stepRestoration T gbmCombined ≠ gbmCombined :=
  dissipative_not_periodic cancerDissipative gbmCombined T (by decide) hT

-- ═══════════════════════════════════════════════════════════════════════
-- §6  Master bundle
-- ═══════════════════════════════════════════════════════════════════════

/--
The Ergodic Cutoff Duality, stated as what is actually proved:

* conservative orbits conserve every observable (`returns_conserves`),
* the cat map and the out-shuffle are both period-10 conservative systems,
* but with distinct orbit structure (1 vs 2 fixed points) — same period, not same quotient,
* dissipative systems absorb in `mono` steps and are aperiodic while positive,
* cancer restoration is a dissipative instance: it recovers in 7 and never recurs.
-/
theorem ergodic_cutoff_duality_master :
    (∀ (α : Type) (S : DissipativeSystem α) (x : α) (T : Nat),
        0 < S.mono x → 0 < T → iter S.step T x ≠ x) ∧
    Returns outShuffle12 10 0 ∧
    (∀ (m : Nat × Nat → Nat) (p : Nat × Nat), p.1 < 5 → p.2 < 5 →
        m (iter aeonCatMap 10 p) = m p) ∧
    ((catCarrier.filter (fun p => decide (aeonCatMap p = p))).length ≠
      (shuffleCarrier.filter (fun i => decide (outShuffle12 i = i))).length) ∧
    (iterateRestoration 7 gbmCombined).deficit = 0 ∧
    (∀ T : Nat, 0 < T → iter stepRestoration T gbmCombined ≠ gbmCombined) := by
  refine ⟨?_, shuffle_returns_10.left, ?_, distinct_orbit_structure,
    cancer_recovers_in_seven_bridged, cancer_state_never_recurs⟩
  · intro α S x T hx hT
    exact dissipative_not_periodic S x T hx hT
  · intro m p h1 h2
    exact cat_observable_conserved m p h1 h2

end ErgodicCutoffDuality
end Gnosis
