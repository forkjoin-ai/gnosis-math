import Init
import Gnosis.AckermannFunction

/-
  AckermannRuntimeCertificate.lean
  =================================

  Lean ledger for the "Ackermann as runtime ceiling" framing.

  `AckermannFunction.ackermannDiag` is the canonical limit of computable
  growth that is **not** primitive recursive. For any runtime function
  `T : Nat → Nat`, the percentage

      T(n) * 100 / ackermannDiag(n)

  measures how close the algorithm sits to that ceiling.
    - 100% = saturating Ackermann (worst-case total computation).
    - Most real code is microscopically below 1% for n ≥ 3.

  This module formalizes the `IsKPercentCertified` predicate and proves
  the six anchor theorems that define the certificate calculus:

    1. `ackermannCeiling_values`          (re-export of `ack_0..ack_3`)
    2. `zero_runtime_zero_percent`        (constant-zero degenerate case)
    3. `ackermann_self_100_percent`       (the saturation witness)
    4. `composition_sum_of_percentages`   (sequential composition law)
    5. `certificate_monotone_in_k`        (slack in the budget)
    6. `certificate_witness_bundle`       (concrete pentad — mirrors
                                           the `pentad` style in
                                           `BowlMeshRuntimeOracle`)

  Sibling files (do NOT live here):
    - `AckermannPrimitiveRecursiveBound.lean` — the eventual-0%
      certificate for every primitive-recursive function.
    - `AckermannRuntimeOracle.lean` — numeric value pins for the Rust
      kernel in `open-source/gnosis/distributed-inference/`.

  Init-only Lean. Zero `sorry`, zero new `axiom`.
-/


namespace AckermannRuntimeCertificate

open AckermannFunction

/-! ## Runtime model -/

/-- A runtime is a function from input size to step count. Total by
    construction (Lean `Nat → Nat` is total — every input has a
    well-defined step count). -/
abbrev Runtime := Nat → Nat

/-- The Ackermann ceiling: re-export of the diagonal already proved in
    `AckermannFunction`. This is the denominator of the
    runtime-certificate metric. -/
def ackermannCeiling (n : Nat) : Nat := ackermannDiag n

/-! ## The certificate predicate

  A runtime `T` is **k-percent Ackermann-certified** when at every
  input size `n`, the step count is at most `k%` of the Ackermann
  ceiling. Stated multiplicatively to stay in `Nat` (no division):

      T n * 100  ≤  k * ackermannCeiling n.

  Rationale for the multiplicative form: Nat division truncates, so
  `T n * 100 / ackermannCeiling n ≤ k` is the wrong claim at `n = 0`
  (where the ceiling is `1` but division by `1` would force exact
  equality). Cross-multiplying keeps the certificate honest at every
  calibration point. -/
def IsKPercentCertified (T : Runtime) (k : Nat) : Prop :=
  ∀ n, T n * 100 ≤ k * ackermannCeiling n

/-! ## Anchor theorem 1 — ceiling values

  The ceiling matches `AckermannFunction.ack_0..ack_3` verbatim. Used
  by `AckermannRuntimeOracle.lean` and by the Rust bench to pin the
  denominator at the small calibration points. -/

/-- **Anchor #1.** The Ackermann ceiling at `n ∈ {0,1,2,3}` matches the
    upstream `ack_0..ack_3` values: `1, 2, 4, 27`. -/
theorem ackermannCeiling_values :
    ackermannCeiling 0 = 1 ∧ ackermannCeiling 1 = 2 ∧
    ackermannCeiling 2 = 4 ∧ ackermannCeiling 3 = 27 :=
  ⟨ack_0, ack_1, ack_2, ack_3⟩

/-! ## Anchor theorem 2 — the zero runtime

  The constant-zero runtime sits at exactly 0% of the ceiling
  everywhere. This is the degenerate floor of the certificate
  lattice. -/

/-- **Anchor #2.** The constant-zero runtime is 0%-certified
    universally: it consumes 0% of the Ackermann ceiling at every `n`. -/
theorem zero_runtime_zero_percent :
    IsKPercentCertified (fun _ => 0) 0 := by
  intro n
  -- LHS: 0 * 100 = 0.  RHS: 0 * ackermannCeiling n = 0.  0 ≤ 0.
  exact Nat.zero_le _

/-! ## Anchor theorem 3 — the saturation witness

  The Ackermann ceiling is 100%-certified by **itself**. This is where
  the "100%" anchor lives: the only runtime that saturates the
  certificate is the Ackermann diagonal. Anything sub-Ackermann is
  strictly below 100% at every large enough `n`. -/

/-- **Anchor #3 (saturation).** `ackermannCeiling` is 100%-certified by
    itself. Reduces to `ackermannCeiling n * 100 = 100 * ackermannCeiling n`
    by `Nat.mul_comm`, then `Nat.le_refl`. -/
theorem ackermann_self_100_percent :
    IsKPercentCertified ackermannCeiling 100 := by
  intro n
  -- Goal: ackermannCeiling n * 100 ≤ 100 * ackermannCeiling n.
  -- By commutativity of Nat multiplication, the two sides are equal.
  rw [Nat.mul_comm (ackermannCeiling n) 100]
  exact Nat.le_refl _

/-! ## Anchor theorem 4 — sequential composition

  If `T1` is `c1`-certified and `T2` is `c2`-certified, then the
  pointwise sum `n ↦ T1 n + T2 n` is `(c1 + c2)`-certified. The bound
  additive part of any sequential-composition reasoning: the budget
  splits across stages and the certified percentages add. -/

/-- **Anchor #4 (composition).** Certificates compose additively across
    sequential stages: if `T1` is `c1`%-certified and `T2` is
    `c2`%-certified, the sum is `(c1 + c2)`%-certified. -/
theorem composition_sum_of_percentages
    (T1 T2 : Runtime) (c1 c2 : Nat)
    (h1 : IsKPercentCertified T1 c1)
    (h2 : IsKPercentCertified T2 c2) :
    IsKPercentCertified (fun n => T1 n + T2 n) (c1 + c2) := by
  intro n
  -- Goal: (T1 n + T2 n) * 100 ≤ (c1 + c2) * ackermannCeiling n.
  -- Distribute both sides and apply the two hypotheses additively.
  rw [Nat.add_mul, Nat.add_mul]
  exact Nat.add_le_add (h1 n) (h2 n)

/-! ## Anchor theorem 5 — monotonicity in the budget

  A `c`-certified runtime is also `c'`-certified for any `c' ≥ c`.
  Spending fewer than `c%` of the ceiling automatically spends fewer
  than `c'%`. -/

/-- **Anchor #5 (monotonicity).** Certificate slack: if `T` fits in
    a `c`-budget and `c ≤ c'`, then `T` also fits in the `c'`-budget. -/
theorem certificate_monotone_in_k
    (T : Runtime) (c c' : Nat) (h_le : c ≤ c')
    (h : IsKPercentCertified T c) :
    IsKPercentCertified T c' := by
  intro n
  -- T n * 100 ≤ c * ceiling n  ≤  c' * ceiling n.
  exact Nat.le_trans (h n) (Nat.mul_le_mul_right (ackermannCeiling n) h_le)

/-! ## Anchor theorem 6 — concrete witness bundle

  Mirrors the `runtime_oracle_pentad` style in
  `BowlMeshRuntimeOracle`: a small bowl of concrete certificates that
  the Rust kernel can reproduce. The witnesses are:

    - **Zero runtime** is 0%-certified universally.
    - **Identity runtime** (`n ↦ n`) is 50%-certified at the
      calibration points `n ∈ {0, 1, 2, 3}`. (Smallest `K` that works:
      `0 ≤ 50·1, 100 ≤ 50·2, 200 ≤ 50·4, 300 ≤ 50·27`.)
    - **Ackermann ceiling** is 100%-certified universally.

  The identity claim is **narrowed to the calibration points** because
  `IsKPercentCertified (fun n => n) 50` for *all* `n` requires
  `2n ≤ ackermannCeiling n`, which is true for `n ≥ 0` from the
  growth ladder but would need an inductive lemma chain to discharge
  here. The Rust bench only needs the calibration-point values; this
  bundle is exactly that contract. -/

theorem certificate_witness_bundle :
    -- (1) Zero runtime is 0%-certified everywhere.
    IsKPercentCertified (fun _ => 0) 0 ∧
    -- (2) Identity runtime is 50%-certified at the calibration
    --     points n ∈ {0, 1, 2, 3}.
    (0 * 100 ≤ 50 * ackermannCeiling 0) ∧
    (1 * 100 ≤ 50 * ackermannCeiling 1) ∧
    (2 * 100 ≤ 50 * ackermannCeiling 2) ∧
    (3 * 100 ≤ 50 * ackermannCeiling 3) ∧
    -- (3) Ackermann ceiling is 100%-certified by itself everywhere.
    IsKPercentCertified ackermannCeiling 100 := by
  refine ⟨zero_runtime_zero_percent, ?_, ?_, ?_, ?_, ackermann_self_100_percent⟩
  · -- n = 0:  0 * 100 = 0  ≤  50 * 1 = 50.
    show 0 * 100 ≤ 50 * ackermannDiag 0
    rw [ack_0]; decide
  · -- n = 1:  1 * 100 = 100  ≤  50 * 2 = 100.
    show 1 * 100 ≤ 50 * ackermannDiag 1
    rw [ack_1]; decide
  · -- n = 2:  2 * 100 = 200  ≤  50 * 4 = 200.
    show 2 * 100 ≤ 50 * ackermannDiag 2
    rw [ack_2]; decide
  · -- n = 3:  3 * 100 = 300  ≤  50 * 27 = 1350.
    show 3 * 100 ≤ 50 * ackermannDiag 3
    rw [ack_3]; decide

end AckermannRuntimeCertificate
