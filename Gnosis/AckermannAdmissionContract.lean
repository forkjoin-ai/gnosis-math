import Init
import Gnosis.AckermannFunction
import Gnosis.AckermannRuntimeCertificate

/-
  AckermannAdmissionContract.lean
  ===============================

  Pins the expected admission verdicts that the Rust admission gate
  (`open-source/gnosis/polyglot/src/ackermann_admission.rs`) must
  reproduce on canonical runtime witnesses.

  Mirrors the canonical *_runtime_oracle_* pattern from
  `BowlMeshRuntimeOracle` / `AmplituhedronFalsifiability` /
  `AckermannRuntimeOracle`. Each theorem here is a Lean-side ground
  truth for a Rust admission decision.

  Imports `Init` plus the two upstream Ackermann modules required for
  `Runtime`, `ackermannCeiling`, and `IsKPercentCertified`. The
  primitive-recursive-bound module is a sibling pattern source, not a
  dependency — the contracts here re-derive their own calibration-
  point arithmetic via `native_decide` against `ackermannDiag`.

  Zero `sorry`, zero new `axiom`. Init-only Lean.
-/


namespace AckermannAdmissionContract

open AckermannFunction
open AckermannRuntimeCertificate

/-! ## Canonical runtime witnesses

Each `runtime_*` is a small `Runtime : Nat → Nat` used as a test
witness in both Lean theorems and the Rust `ackermann_admission::tests`
module. The Rust gate's `decide_admission` on these witnesses must
produce verdicts consistent with the theorems below. -/

/-- The zero runtime: `T(n) = 0` everywhere. The trivial primitive-
    recursive case. The Rust gate MUST admit (verdict
    `AdmitPrimitiveRecursive`). -/
def runtime_zero : Runtime := fun _ => 0

/-- The identity runtime: `T(n) = n`. Linear, primitive-recursive.
    The Rust gate MUST admit (verdict
    `AdmitPrimitiveRecursive { degree_estimate: 1 }`). -/
def runtime_identity : Runtime := fun n => n

/-- The quadratic runtime: `T(n) = n * n`. Primitive-recursive,
    degree 2. The Rust gate MUST admit (verdict
    `AdmitPrimitiveRecursive { degree_estimate: 2 }`). -/
def runtime_quadratic : Runtime := fun n => n * n

/-- The Ackermann-saturating runtime: `T(n) = ackermannCeiling n`.
    Sits exactly at the 100% ceiling. The contract here pins the
    structural equality `T n * 100 = 100 * ackermannCeiling n` at
    each calibration point; the Rust gate's *policy* at exactly 100%
    (admit-with-legacy-guards vs reject) is documented on the Rust
    side, not pinned here. -/
def runtime_ackermann_saturating : Runtime := ackermannCeiling

/-- An over-ceiling runtime: `T(n) = 2 * ackermannCeiling n`. At
    every calibration point this is strictly above 100%, so the Rust
    gate MUST emit `Reject(ExceedsCeilingAtCalibration)`. -/
def runtime_over_ceiling : Runtime := fun n => 2 * ackermannCeiling n

/-! ## Admission contracts

Each theorem pins the expected verdict for one canonical witness on
the calibration window `{0, 1, 2, 3}`. The Rust
`ackermann_admission::tests` module must produce results consistent
with these. -/

/-- **Admission contract #1.** Zero runtime is 0%-certified
    universally — every input yields 0 steps, which is trivially `≤`
    any multiple of the ceiling. The Rust gate MUST return
    `AdmitPrimitiveRecursive`. -/
theorem zero_runtime_admission_contract :
    IsKPercentCertified runtime_zero 0 := by
  intro n
  -- LHS: runtime_zero n * 100 = 0 * 100 = 0.
  -- RHS: 0 * ackermannCeiling n = 0. Then 0 ≤ 0.
  show 0 * 100 ≤ 0 * ackermannCeiling n
  exact Nat.zero_le _

/-- **Admission contract #2.** Identity runtime is 50%-certified on
    the calibration window. (See
    `identity_runtime_50_percent_at_calibration` in the sibling
    `AckermannPrimitiveRecursiveBound` module for the same
    arithmetic.) The Rust gate MUST return
    `AdmitPrimitiveRecursive { degree_estimate: 1 }`. -/
theorem identity_runtime_admission_contract :
    runtime_identity 0 * 100 ≤ 50 * ackermannCeiling 0 ∧
    runtime_identity 1 * 100 ≤ 50 * ackermannCeiling 1 ∧
    runtime_identity 2 * 100 ≤ 50 * ackermannCeiling 2 ∧
    runtime_identity 3 * 100 ≤ 50 * ackermannCeiling 3 := by
  unfold runtime_identity ackermannCeiling ackermannDiag
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide

/-- **Admission contract #3.** Quadratic runtime is admitted on the
    calibration window at `K = 100`. Tightest-K computation by hand:

      n=0:   0 ≤ K·1   ⇒ K ≥ 0
      n=1: 100 ≤ K·2   ⇒ K ≥ 50
      n=2: 400 ≤ K·4   ⇒ K ≥ 100
      n=3: 900 ≤ K·27  ⇒ K ≥ 34 (since 900/27 ≈ 33.33)

    So K = 100 admits cleanly on the window. The Rust gate MUST
    return `AdmitPrimitiveRecursive { degree_estimate: 2 }`. -/
theorem quadratic_runtime_admission_contract :
    runtime_quadratic 0 * 100 ≤ 100 * ackermannCeiling 0 ∧
    runtime_quadratic 1 * 100 ≤ 100 * ackermannCeiling 1 ∧
    runtime_quadratic 2 * 100 ≤ 100 * ackermannCeiling 2 ∧
    runtime_quadratic 3 * 100 ≤ 100 * ackermannCeiling 3 := by
  unfold runtime_quadratic ackermannCeiling ackermannDiag
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide

/-- **Admission contract #4.** The Ackermann-saturating runtime sits
    exactly at the 100% ceiling at every calibration point —
    pointwise equality, not just `≤`. The contract pins the structural
    identity; the Rust gate's policy at exactly 100% (admit-with-
    legacy-guards vs reject) is a Rust-side decision documented in
    `ackermann_admission.rs`, not pinned here. The Rust gate MUST
    return `Reject(ExceedsCeilingAtCalibration)` for any runtime that
    strictly exceeds this profile (see contract #5). -/
theorem ackermann_saturating_admission_contract :
    runtime_ackermann_saturating 0 * 100 = 100 * ackermannCeiling 0 ∧
    runtime_ackermann_saturating 1 * 100 = 100 * ackermannCeiling 1 ∧
    runtime_ackermann_saturating 2 * 100 = 100 * ackermannCeiling 2 ∧
    runtime_ackermann_saturating 3 * 100 = 100 * ackermannCeiling 3 := by
  unfold runtime_ackermann_saturating ackermannCeiling ackermannDiag
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide

/-- **Admission contract #5.** The over-ceiling runtime is strictly
    above the 100% ceiling at every calibration point. Concretely
    `2 * ackermannCeiling n * 100 > 100 * ackermannCeiling n` reduces
    to `200 * c > 100 * c` for `c ≥ 1`, decidable at each fixed n.
    The Rust gate MUST return `Reject(ExceedsCeilingAtCalibration)`. -/
theorem over_ceiling_admission_contract :
    runtime_over_ceiling 0 * 100 > 100 * ackermannCeiling 0 ∧
    runtime_over_ceiling 1 * 100 > 100 * ackermannCeiling 1 ∧
    runtime_over_ceiling 2 * 100 > 100 * ackermannCeiling 2 ∧
    runtime_over_ceiling 3 * 100 > 100 * ackermannCeiling 3 := by
  unfold runtime_over_ceiling ackermannCeiling ackermannDiag
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide

/-! ## Bundled pentad

A single statement carrying the five admission contracts. The Rust
test module mirrors this point-for-point, evaluating
`decide_admission` on each of the five canonical runtime witnesses
and checking the verdict matches the contract pinned here. -/

/-- **Bundled admission pentad.** Single statement carrying all five
    admission contracts; the Rust test surface in
    `ackermann_admission.rs::tests` exercises this pentad point-for-
    point. Conjuncts in order:

    1. zero runtime — universal 0%-certification (admit),
    2. identity runtime at n = 3 — 50%-window certification (admit),
    3. quadratic runtime at n = 3 — 100%-window certification (admit),
    4. Ackermann-saturating runtime at n = 3 — equality at 100%
       (policy-dependent verdict on the Rust side),
    5. over-ceiling runtime at n = 3 — strict exceedance (reject). -/
theorem ackermann_admission_pentad :
    IsKPercentCertified runtime_zero 0 ∧
    (runtime_identity 3 * 100 ≤ 50 * ackermannCeiling 3) ∧
    (runtime_quadratic 3 * 100 ≤ 100 * ackermannCeiling 3) ∧
    (runtime_ackermann_saturating 3 * 100 = 100 * ackermannCeiling 3) ∧
    (runtime_over_ceiling 3 * 100 > 100 * ackermannCeiling 3) :=
  ⟨zero_runtime_admission_contract,
   identity_runtime_admission_contract.2.2.2,
   quadratic_runtime_admission_contract.2.2.2,
   ackermann_saturating_admission_contract.2.2.2,
   over_ceiling_admission_contract.2.2.2⟩

end AckermannAdmissionContract
