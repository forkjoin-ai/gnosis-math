import Init

/-!
# Fibonacci Pisano Period Phase Map (Void Archaeology)

Extends `FibLucasExtendedIdentities.lean`, `QuadraticReciprocityInstances.lean`,
`VoidArchaeology.lean`, and `CountBadLucasPhaseReconstruction.lean`.

## The phase-structured unknowable

The Pisano period `π(p)` is the smallest positive `n` with
`F_n ≡ 0 (mod p)` and `F_{n+1} ≡ 1 (mod p)`. The general closed form
is wall-blocked — it depends on the splitting behavior of `x² − x − 1`
over `ℤ/pℤ`, which requires algebraic-number-field machinery.

Ring-extension wall. But the phase structure is decidable at each prime:

  If `(5/p) = 1`  (i.e., `p mod 5 ∈ {1, 4}`):  `π(p) | p − 1`
  If `(5/p) = −1` (i.e., `p mod 5 ∈ {2, 3}`):  `π(p) | 2(p + 1)`

This mirrors the phase structure recovered in
`CountBadLucasPhaseReconstruction`. The unknowable (closed form of `π`)
sits behind a wall; its shape is reconstructable by aggressive witness
gathering on both phases.

## What this module does

Implements `fibIterMod p n` computing `(F_n mod p, F_{n+1} mod p)`
without leaving `Init` or `Nat`. For ten primes split across the two
phases, witnesses:

- **Positive (period identity)**: `fibIterMod p π(p) = (0, 1)`.
- **Phase constraint**: either `π(p) | p − 1` (phase 1) or
  `π(p) | 2(p + 1)` (phase 2) — never both phases for the same prime.
- **Negative (phase failure)**: the opposite phase constraint FAILS.
  Scraping the void at the other side of the phase boundary.

Five primes per phase. The phase assignment is witnessed by the
residue `p mod 5`.

## What this module does NOT claim

- No proof that `π(p)` is as listed — Pisano values are hard-coded from
  OEIS A001175 and verified pointwise as periodic witnesses, not
  derived. The *minimality* of `π(p)` (no smaller `k` with the
  identity) is not part of the phase reconstruction; the divisibility
  phase only needs one matching `n` to anchor.
- No proof that `p mod 5` controls the phase universally — only
  witnessed at the enumerated primes. The general theorem sits behind
  the ring-extension wall.
- No Legendre-symbol computation here — it is observed directly as
  `p mod 5 ∈ {1,4}` vs `{2,3}`.

`import Init` only. Zero `sorry`, zero new `axiom`.
-/

namespace Gnosis
namespace FibonacciPisanoPhaseMap

/-! ## Fibonacci mod m (pair-iteration) -/

/-- One step of Fibonacci iteration mod m. State is the pair
`(F_n mod m, F_{n+1} mod m)`. -/
def fibStepMod (m : Nat) (s : Nat × Nat) : Nat × Nat :=
  (s.2, (s.1 + s.2) % m)

/-- Iterate `fibStepMod` starting from `(F_0, F_1) = (0, 1)`. -/
def fibIterMod (m : Nat) : Nat → Nat × Nat
  | 0     => (0, 1)
  | n + 1 => fibStepMod m (fibIterMod m n)

/-! ## Phase-1 primes: `p mod 5 ∈ {1, 4}`, `π(p) | p − 1`

For each such prime we witness:
1. The Pisano period identity at the tabulated `π(p)`.
2. The phase-1 divisibility: `π(p) | p − 1`.
3. The phase-2 divisibility FAILS: `¬ (π(p) | 2(p + 1))`.

The negative witness is deliberate — it scrapes the opposite phase
boundary. -/

/-! ### p = 11, π = 10, 11 mod 5 = 1 -/

theorem mod5_11 : 11 % 5 = 1 := by decide
theorem pisano_11_at_10 : fibIterMod 11 10 = (0, 1) := by decide
theorem phase1_11 : (11 - 1) % 10 = 0 := by decide
theorem phase2_fails_11 : (2 * (11 + 1)) % 10 ≠ 0 := by decide

/-! ### p = 19, π = 18, 19 mod 5 = 4 -/

theorem mod5_19 : 19 % 5 = 4 := by decide
theorem pisano_19_at_18 : fibIterMod 19 18 = (0, 1) := by decide
theorem phase1_19 : (19 - 1) % 18 = 0 := by decide
theorem phase2_fails_19 : (2 * (19 + 1)) % 18 ≠ 0 := by decide

/-! ### p = 29, π = 14, 29 mod 5 = 4. Note π divides p - 1 = 28. -/

theorem mod5_29 : 29 % 5 = 4 := by decide
theorem pisano_29_at_14 : fibIterMod 29 14 = (0, 1) := by decide
theorem phase1_29 : (29 - 1) % 14 = 0 := by decide
theorem phase2_fails_29 : (2 * (29 + 1)) % 14 ≠ 0 := by decide

/-! ### p = 31, π = 30, 31 mod 5 = 1 -/

theorem mod5_31 : 31 % 5 = 1 := by decide
theorem pisano_31_at_30 : fibIterMod 31 30 = (0, 1) := by decide
theorem phase1_31 : (31 - 1) % 30 = 0 := by decide
theorem phase2_fails_31 : (2 * (31 + 1)) % 30 ≠ 0 := by decide

/-! ### p = 41, π = 40, 41 mod 5 = 1 -/

theorem mod5_41 : 41 % 5 = 1 := by decide
theorem pisano_41_at_40 : fibIterMod 41 40 = (0, 1) := by decide
theorem phase1_41 : (41 - 1) % 40 = 0 := by decide
theorem phase2_fails_41 : (2 * (41 + 1)) % 40 ≠ 0 := by decide

/-! ## Phase-2 primes: `p mod 5 ∈ {2, 3}`, `π(p) | 2(p + 1)`

Deliberately scraped on the opposite side. -/

/-! ### p = 3, π = 8, 3 mod 5 = 3 -/

theorem mod5_3 : 3 % 5 = 3 := by decide
theorem pisano_3_at_8 : fibIterMod 3 8 = (0, 1) := by decide
theorem phase2_3 : (2 * (3 + 1)) % 8 = 0 := by decide
theorem phase1_fails_3 : (3 - 1) % 8 ≠ 0 := by decide

/-! ### p = 7, π = 16, 7 mod 5 = 2 -/

theorem mod5_7 : 7 % 5 = 2 := by decide
theorem pisano_7_at_16 : fibIterMod 7 16 = (0, 1) := by decide
theorem phase2_7 : (2 * (7 + 1)) % 16 = 0 := by decide
theorem phase1_fails_7 : (7 - 1) % 16 ≠ 0 := by decide

/-! ### p = 13, π = 28, 13 mod 5 = 3 -/

theorem mod5_13 : 13 % 5 = 3 := by decide
theorem pisano_13_at_28 : fibIterMod 13 28 = (0, 1) := by decide
theorem phase2_13 : (2 * (13 + 1)) % 28 = 0 := by decide
theorem phase1_fails_13 : (13 - 1) % 28 ≠ 0 := by decide

/-! ### p = 17, π = 36, 17 mod 5 = 2 -/

theorem mod5_17 : 17 % 5 = 2 := by decide
theorem pisano_17_at_36 : fibIterMod 17 36 = (0, 1) := by decide
theorem phase2_17 : (2 * (17 + 1)) % 36 = 0 := by decide
theorem phase1_fails_17 : (17 - 1) % 36 ≠ 0 := by decide

/-! ### p = 23, π = 48, 23 mod 5 = 3 -/

set_option maxRecDepth 2048 in
theorem pisano_23_at_48 : fibIterMod 23 48 = (0, 1) := by decide

theorem mod5_23 : 23 % 5 = 3 := by decide
theorem phase2_23 : (2 * (23 + 1)) % 48 = 0 := by decide
theorem phase1_fails_23 : (23 - 1) % 48 ≠ 0 := by decide

/-! ## Phase-determining witness

For every enumerated prime, exactly one phase holds. The phase is
predicted by `p mod 5`. -/

/-- Given `p` and `π`, returns `true` iff the phase-1 constraint holds
(`π | p − 1`). -/
def phase1Holds (p π : Nat) : Bool :=
  decide ((p - 1) % π = 0)

/-- Given `p` and `π`, returns `true` iff the phase-2 constraint holds
(`π | 2(p + 1)`). -/
def phase2Holds (p π : Nat) : Bool :=
  decide ((2 * (p + 1)) % π = 0)

/-- The phase is determined by `p mod 5 ∈ {1, 4}` (phase 1) vs
`p mod 5 ∈ {2, 3}` (phase 2). -/
def predictedPhase1 (p : Nat) : Bool :=
  decide (p % 5 = 1) || decide (p % 5 = 4)

/-! ### Phase prediction consistency -/

theorem prediction_11 : predictedPhase1 11 = true ∧ phase1Holds 11 10 = true := by decide
theorem prediction_19 : predictedPhase1 19 = true ∧ phase1Holds 19 18 = true := by decide
theorem prediction_29 : predictedPhase1 29 = true ∧ phase1Holds 29 14 = true := by decide
theorem prediction_31 : predictedPhase1 31 = true ∧ phase1Holds 31 30 = true := by decide
theorem prediction_41 : predictedPhase1 41 = true ∧ phase1Holds 41 40 = true := by decide

theorem prediction_3  : predictedPhase1 3  = false ∧ phase2Holds 3  8  = true := by decide
theorem prediction_7  : predictedPhase1 7  = false ∧ phase2Holds 7  16 = true := by decide
theorem prediction_13 : predictedPhase1 13 = false ∧ phase2Holds 13 28 = true := by decide
theorem prediction_17 : predictedPhase1 17 = false ∧ phase2Holds 17 36 = true := by decide
theorem prediction_23 : predictedPhase1 23 = false ∧ phase2Holds 23 48 = true := by decide

/-! ## Master witness

10 primes split 5-5 across the two phases. For every one, the
divisibility holds in the predicted phase AND fails in the opposite
phase. The `p mod 5` residue perfectly predicts. -/

set_option maxRecDepth 2048 in
theorem pisano_phase_reconstruction :
    -- Phase 1: p mod 5 ∈ {1, 4}, π | p - 1, and π ∤ 2(p+1)
    (fibIterMod 11 10 = (0, 1) ∧ (11 - 1) % 10 = 0 ∧ (2 * 12) % 10 ≠ 0)
    ∧ (fibIterMod 19 18 = (0, 1) ∧ (19 - 1) % 18 = 0 ∧ (2 * 20) % 18 ≠ 0)
    ∧ (fibIterMod 29 14 = (0, 1) ∧ (29 - 1) % 14 = 0 ∧ (2 * 30) % 14 ≠ 0)
    ∧ (fibIterMod 31 30 = (0, 1) ∧ (31 - 1) % 30 = 0 ∧ (2 * 32) % 30 ≠ 0)
    ∧ (fibIterMod 41 40 = (0, 1) ∧ (41 - 1) % 40 = 0 ∧ (2 * 42) % 40 ≠ 0)
    -- Phase 2: p mod 5 ∈ {2, 3}, π | 2(p+1), and π ∤ p - 1
    ∧ (fibIterMod 3  8  = (0, 1) ∧ (2 * 4)  % 8  = 0 ∧ (3 - 1)  % 8  ≠ 0)
    ∧ (fibIterMod 7  16 = (0, 1) ∧ (2 * 8)  % 16 = 0 ∧ (7 - 1)  % 16 ≠ 0)
    ∧ (fibIterMod 13 28 = (0, 1) ∧ (2 * 14) % 28 = 0 ∧ (13 - 1) % 28 ≠ 0)
    ∧ (fibIterMod 17 36 = (0, 1) ∧ (2 * 18) % 36 = 0 ∧ (17 - 1) % 36 ≠ 0)
    ∧ (fibIterMod 23 48 = (0, 1) ∧ (2 * 24) % 48 = 0 ∧ (23 - 1) % 48 ≠ 0) := by
  decide

/-! ## Epistemic status

The unknowable: general Pisano period closed form. Sits behind the
ring-extension wall (needs splitting of `x² − x − 1` mod p, which lives
in `ℤ[φ]`, an algebraic extension).

What the void archaeology reveals:
- `p mod 5 ∈ {1, 4}` → phase 1 (`π | p − 1`)
- `p mod 5 ∈ {2, 3}` → phase 2 (`π | 2(p + 1)`)
- The phase IS the Legendre symbol `(5/p)`, by quadratic reciprocity
  with the law `(5/p) = (p/5)` (since `5 ≡ 1 mod 4`). So the phase
  reduction `p mod 5` encodes a quadratic reciprocity statement.

The ring-extension wall still separates us from proof; ten pairwise
witnesses across the two phases are a dense-enough projection that the
shape of what lies beyond the wall is visible from this side.

## What this suggests next

- `FibPeriodBoundaryPhase.lean` — distinguish primes where the phase
  divisor bound is tight (`π(p) = p − 1` exactly, or `π(p) = 2(p + 1)`
  exactly) from those where it is strict (`π | p − 1` but `π < p − 1`).
  The "tight vs strict" distinction is another layer of phase structure
  on top of the divisibility phase.
- `LucasPrimePhase.lean` — the same phase map for the Lucas sequence:
  `L_n mod p` has its own period, equal to `π(p)` in most cases and
  exactly half in some. The exceptions are a third-order phase
  marker inside the Pisano phase.
-/

end FibonacciPisanoPhaseMap
end Gnosis
