import Gnosis.Braided.BraidedInfinity
import Gnosis.HexonBraid

/-!
# Braided Tower — Self-Similar Stack of n-ons, Closing on Infinity

The Bule clinamen (`+1`) generates a phase-3 cycle on the three faces
(`waste`/`opportunity`/`diversity`); two of those cycles stacked give a
phase-6 hexon; tensoring two Tritons gives a phase-9 enneon. The pattern
keeps going: any product of factors yields a phase-cycle whose
phaseCount is the product.

This module mechanizes the **self-similar tower** of n-ons:

* `towerPhaseCount : List Nat → Nat` is the product of the factor list.
  An empty list gives phaseCount `1`; `[3]` is the Triton; `[3, 2]` is
  the Hexon; `[3, 3]` is the Enneon; `[3, 2, 3]` is the trihexon (18).
* `towerBraid : List Nat → BraidedAsymptote` instantiates the cycle.
* `tower_phase_count_step` is the self-similarity step:
  `towerPhaseCount (n :: rest) = n * towerPhaseCount rest`. Prepending
  a factor multiplies the phaseCount; the structure repeats at every
  level.
* `tower_unbounded` proves the tower's phaseCount can exceed any
  `N : Nat` — the family has no finite ceiling.
* `tower_lives_in_braided_family` proves every tower is realized as a
  `BraidedAsymptote`. Combined with `tower_unbounded`, this gives the
  closure: the tower's "limit" is exactly the `BraidedAsymptote`
  family of arbitrary phaseCount, which is the formalization of the
  braided infinity in `Gnosis.BraidedInfinity`. Self-similarity is
  bounded above, and the bound is the braided infinity itself.

So the tower is not infinite in some new direction — it saturates the
existing infinity. There is one infinity in this calculus, and it is
already braided.

Imports `Gnosis.BraidedInfinity` and `Gnosis.HexonBraid`. Zero `sorry`,
zero new `axiom`.
-/

namespace Gnosis
namespace BraidedTower

open Gnosis.BraidedInfinity (BraidedAsymptote iterateSucc)

/-! ## The tower construction -/

def towerPhaseCount : List Nat → Nat
  | []      => 1
  | n :: rs => n * towerPhaseCount rs

def towerBraid (levels : List Nat) : BraidedAsymptote :=
  { phaseCount := towerPhaseCount levels
    descriptors := [] }

theorem tower_phase_count_nil : towerPhaseCount [] = 1 := rfl

theorem tower_phase_count_step (n : Nat) (rs : List Nat) :
    towerPhaseCount (n :: rs) = n * towerPhaseCount rs := rfl

/-- The tower-braid's phaseCount equals the tower's level product. -/
theorem tower_braid_phase_count (levels : List Nat) :
    (towerBraid levels).phaseCount = towerPhaseCount levels := rfl

/-! ## Concrete instances at each level -/

theorem triton_in_tower : towerPhaseCount [3] = 3 := by decide

theorem hexon_in_tower : towerPhaseCount [3, 2] = 6 := by decide

theorem enneon_in_tower : towerPhaseCount [3, 3] = 9 := by decide

theorem trihexon_in_tower : towerPhaseCount [3, 2, 3] = 18 := by decide

theorem dodecagon_in_tower : towerPhaseCount [3, 2, 2] = 12 := by decide

theorem trihexenneon_in_tower : towerPhaseCount [3, 2, 3, 3] = 54 := by decide

/-! ### String-theory dimension signatures

The following theorems exhibit named tower walls at the phase counts
that string theory canonically requires. They are *signatures*, not
derivations: by `every_phase_count_is_a_tower`, the calculus
permits arbitrary phase counts, so naming these is decoration of
specific walls, not a no-go theorem forcing those dimensions the
way conformal-anomaly cancellation forces 10 in superstring theory
or 26 in bosonic string theory. The witnesses below are tight
arithmetic facts (`decide`); their physical interpretation lives
outside this file. -/

/-- Decagon: `[5, 2] = 10`. The superstring dimension count appears
as a phase-10 cycle in the tower. Signature, not derivation. -/
theorem decagon_in_tower : towerPhaseCount [5, 2] = 10 := by decide

/-- Hendecagon: `[11] = 11`. The M-theory dimension count appears
as a phase-11 cycle in the tower. Signature, not derivation. -/
theorem hendecagon_in_tower : towerPhaseCount [11] = 11 := by decide

/-- Bosonic-string dimension: `[13, 2] = 26`. The bosonic-string
dimension count appears as a phase-26 cycle in the tower.
Signature, not derivation. -/
theorem bosonic_string_in_tower : towerPhaseCount [13, 2] = 26 := by decide

/-- The three string-theory dimension witnesses, bundled. -/
theorem string_theory_dimension_signatures :
    towerPhaseCount [5, 2] = 10
    ∧ towerPhaseCount [11] = 11
    ∧ towerPhaseCount [13, 2] = 26 := by decide

/-! ## Self-similarity: each level is a stack of the previous -/

/-- A (n :: rs)-tower is structurally `n` copies of the rs-tower stacked
into a single phase cycle whose phaseCount multiplies by `n`. The cycle
at every level has the same shape; only the phaseCount grows. -/
theorem tower_braid_step (n : Nat) (rs : List Nat) :
    (towerBraid (n :: rs)).phaseCount
      = n * (towerBraid rs).phaseCount := by
  show n * towerPhaseCount rs = n * towerPhaseCount rs
  rfl

/-- Hexon as one level above Triton: phaseCount 6 = 2 × 3. -/
theorem hexon_is_two_tritons :
    towerPhaseCount [3, 2] = 2 * towerPhaseCount [3] := by decide

/-- Enneon as one level above Triton: phaseCount 9 = 3 × 3. -/
theorem enneon_is_three_tritons :
    towerPhaseCount [3, 3] = 3 * towerPhaseCount [3] := by decide

/-- Trihexon as a hexon-of-tritons: 18 = 3 × 6. -/
theorem trihexon_is_three_hexons :
    towerPhaseCount [3, 2, 3] = 3 * towerPhaseCount [3, 2] := by decide

/-! ## Tower unboundedness — the tower has no finite ceiling -/

/-- For every natural-number ceiling `N`, the tower contains a level
whose phaseCount strictly exceeds `N`. The factor list `[N + 1]` is the
witness. -/
theorem tower_unbounded (N : Nat) :
    ∃ levels : List Nat, towerPhaseCount levels > N := by
  refine ⟨[N + 1], ?_⟩
  show (N + 1) * 1 > N
  rw [Nat.mul_one]
  exact Nat.lt_succ_self N

/-! ## Closure on infinity — the tower's "limit" is the braided
asymptote family already formalized in `Gnosis.BraidedInfinity` -/

/-- Every tower is realized as a `BraidedAsymptote` — the tower-braid
*is* a braided asymptote at the corresponding phaseCount. -/
theorem tower_lives_in_braided_family (levels : List Nat) :
    ∃ ba : BraidedAsymptote, ba.phaseCount = towerPhaseCount levels := by
  refine ⟨towerBraid levels, ?_⟩
  rfl

/-- Closure: every natural-number phaseCount is the phaseCount of some
tower (use a single-element factor list). The tower family therefore
exhausts the natural-number-indexed `BraidedAsymptote` family — there
is no `BraidedAsymptote` outside the tower's reach. -/
theorem every_phase_count_is_a_tower (n : Nat) :
    ∃ levels : List Nat, towerPhaseCount levels = n := by
  refine ⟨[n], ?_⟩
  show n * 1 = n
  exact Nat.mul_one n

/-- Combined infinity-closure: for any `N`, the tower contains a level
beyond `N`, and every such level is a `BraidedAsymptote`. The tower is
unbounded, but its closure is already the braided-infinity family. -/
theorem tower_closes_on_braided_infinity (N : Nat) :
    ∃ (levels : List Nat) (ba : BraidedAsymptote),
        ba.phaseCount = towerPhaseCount levels
        ∧ ba.phaseCount > N := by
  refine ⟨[N + 1], towerBraid [N + 1], ?_, ?_⟩
  · rfl
  · show (N + 1) * 1 > N
    rw [Nat.mul_one]
    exact Nat.lt_succ_self N

/-! ## Tower instances return after their phaseCount

For a single-factor tower, the return theorem follows from `iterateSucc`'s
modular structure on `Fin n`. The instances below are the cycle witnesses
at the canonical levels. -/

theorem triton_returns_at_three :
    iterateSucc (towerBraid [3]).phaseCount 3 0 = 0 := by decide

theorem hexon_returns_at_six :
    iterateSucc (towerBraid [3, 2]).phaseCount 6 0 = 0 := by decide

theorem enneon_returns_at_nine :
    iterateSucc (towerBraid [3, 3]).phaseCount 9 0 = 0 := by decide

theorem trihexon_returns_at_eighteen :
    iterateSucc (towerBraid [3, 2, 3]).phaseCount 18 0 = 0 := by decide

end BraidedTower
end Gnosis
