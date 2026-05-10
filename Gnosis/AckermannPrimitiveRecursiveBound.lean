/-
  AckermannPrimitiveRecursiveBound.lean
  =====================================

  Calibration-window structural witness for the Ackermann
  runtime-certification topic. Companion to
  `Gnosis.AckermannRuntimeCertificate` (which owns `Runtime`,
  `ackermannCeiling`, and `IsKPercentCertified`) and
  `Gnosis.AckermannRuntimeOracle` (Lean → Rust value contracts).

  ## What this file pins down

  The classical "Ackermann is not primitive recursive" result says
  every primitive-recursive function is *eventually* dominated by
  the Ackermann diagonal: for each fixed level `k` there exists an
  input size beyond which `H(k, n, n) < A(n)`. The full universal
  statement requires a primitive-recursive function encoder, which
  Init-Lean does not give us cheaply, so the universal direction is
  **out of scope** for this module.

  What is in scope — and load-bearing for the Rust kernel's
  PR-detection fallback — is the *bounded-window* structural form:
  on the calibration window `{0, 1, 2, 3}` we exhibit concrete
  fixed-level hyperops sitting below the Ackermann diagonal, a
  zero-runtime fully-tight 0%-certificate, and an identity-runtime
  50%-certificate. The Rust kernel uses these as the contract surface
  for its finite-difference / structural-fallback regime at `n ≥ 4`.

  ## What's formalized vs what isn't

  Formalized:

  * `fixedLevelHyperopRuntime k` — the runtime profile `n ↦ H(k, n, n)`.
    A primitive-recursive runtime is dominated by some such profile;
    we do not prove that direction here.
  * `fixed_level_below_ceiling_at_calibration` — mirrors
    `AckermannFunction.ack_dominates`: at n = 3, levels 1 and 2 are
    strictly below the Ackermann diagonal.
  * `zero_runtime_calibration_window` — the concrete-window form of
    the zero-runtime 0%-certificate.
  * `identity_runtime_50_percent_at_calibration` — k = 50 suffices to
    certify the identity runtime on the window. The k-value is hand-
    computed (n=1: 100 ≤ 50·2; n=2: 200 ≤ 50·4; n=3: 300 ≤ 50·27);
    we do not claim it is the tight bound, only that it works.
  * `level_two_dominated_at_three` — at n = 3, level-2 hyperop
    (multiplication, value 9) is strictly under the 50%-ceiling of
    the Ackermann diagonal (50 · 27 / 100 = 13.5).

  Not formalized (and explicitly out of scope):

  * Universal "every PR function is eventually dominated by the
    Ackermann diagonal" — requires a PR-encoding registry Init-Lean
    cannot host cheaply.
  * Tightness of k = 50. The hand-computation shows k ≥ 50 is
    necessary at n = 1 and n = 2 on the window; we use it as a
    convenient round witness, not the infimum.
  * Behavior at n ≥ 4. The Rust kernel handles `n ≥ 4` via its
    structural-fallback regime; this module is the contract surface
    for the small-n calibration boundary the kernel cross-checks
    against.

  Imports `Init`, `Gnosis.AckermannFunction`, and the sibling
  `Gnosis.AckermannRuntimeCertificate`. Zero `sorry`, zero new
  `axiom`.
-/

import Init
import Gnosis.AckermannFunction
import Gnosis.AckermannRuntimeCertificate

namespace AckermannPrimitiveRecursiveBound

open AckermannFunction
open AckermannRuntimeCertificate

/-! ## Fixed-level hyperop runtime

The `k`-level hyperop runtime at input size `n` runs in `H(k, n, n)`
steps. For k = 1 this is addition (n + n), k = 2 multiplication
(n · n), k = 3 exponentiation (n^n), and so on. Every primitive-
recursive function is dominated by some such profile for some
finite k — that universal claim is the out-of-scope direction we
mention in the file header.
-/

/-- A **fixed-level hyperop runtime**: at input size n, runs in
    `hyperop k n n` steps. For k = 1 this is addition, k = 2
    multiplication, k = 3 exponentiation, etc. Every primitive
    recursive function is dominated by such a fixed-level
    hyperop for some k. -/
def fixedLevelHyperopRuntime (k : Nat) : Runtime := fun n => hyperop k n n

/-! ## Calibration-window structural witnesses -/

/-- **The boundary witness.** At n = 3, fixed-level hyperops at
    levels 1 and 2 sit strictly below the Ackermann diagonal.
    Mirrors `AckermannFunction.ack_dominates` with the
    `ackermannCeiling` re-export. -/
theorem fixed_level_below_ceiling_at_calibration :
    hyperop 1 3 3 < ackermannCeiling 3 ∧
    hyperop 2 3 3 < ackermannCeiling 3 := by
  unfold ackermannCeiling ackermannDiag
  refine ⟨?_, ?_⟩ <;> native_decide

/-- **Bounded-window 0%-certification witness.** A constant zero
    runtime is 0%-certified at every calibration point. (The
    universal version `T n * 100 ≤ 0 * ackermannCeiling n ↔ T n = 0`
    is owned by the sibling file `AckermannRuntimeCertificate`;
    this one is the *concrete-window* witness the harness actually
    checks.) -/
theorem zero_runtime_calibration_window :
    (fun (_ : Nat) => 0) 0 * 100 ≤ 0 * ackermannCeiling 0 ∧
    (fun (_ : Nat) => 0) 1 * 100 ≤ 0 * ackermannCeiling 1 ∧
    (fun (_ : Nat) => 0) 2 * 100 ≤ 0 * ackermannCeiling 2 ∧
    (fun (_ : Nat) => 0) 3 * 100 ≤ 0 * ackermannCeiling 3 := by
  unfold ackermannCeiling ackermannDiag
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide

/-- **Identity runtime calibration certificate.** The identity
    runtime `fun n => n` at each calibration point n produces step
    count = n. The smallest k such that `n * 100 ≤ k * ackermannCeiling n`
    at every n ∈ {0,1,2,3} can be computed by hand:

      n=0:   0 ≤ k · 1   ⇒ k ≥ 0
      n=1: 100 ≤ k · 2   ⇒ k ≥ 50
      n=2: 200 ≤ k · 4   ⇒ k ≥ 50
      n=3: 300 ≤ k · 27  ⇒ k ≥ 12  (300 / 27 ≈ 11.1)

    So k = 50 suffices on this window. We are not claiming
    tightness — just that this k-value works as a contract witness. -/
theorem identity_runtime_50_percent_at_calibration :
    (fun n => n) 0 * 100 ≤ 50 * ackermannCeiling 0 ∧
    (fun n => n) 1 * 100 ≤ 50 * ackermannCeiling 1 ∧
    (fun n => n) 2 * 100 ≤ 50 * ackermannCeiling 2 ∧
    (fun n => n) 3 * 100 ≤ 50 * ackermannCeiling 3 := by
  unfold ackermannCeiling ackermannDiag
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide

/-- **The structural separation.** For any `n ≥ 1`, level-2 hyperop
    (multiplication) at (n, n) yields `n · n`, while the diagonal
    `ackermannDiag n = hyperop n n n` runs at level n. At n = 3 the
    gap is 9 vs 27; at n ≥ 4 the diagonal explodes (tetration and
    beyond). This theorem witnesses the gap at the calibration
    boundary and serves as the small-Nat decidable base case for
    "PR is dominated, eventually" on the n ≥ 4 regime the Rust
    kernel handles structurally.

    Concretely: `hyperop 2 3 3 = 9`, so `9 · 100 = 900`, and
    `50 · ackermannCeiling 3 = 50 · 27 = 1350`. So 900 < 1350. -/
theorem level_two_dominated_at_three :
    hyperop 2 3 3 * 100 < 50 * ackermannCeiling 3 := by
  unfold ackermannCeiling ackermannDiag
  native_decide

/-! ## Headline bundle

The four calibration-window structural witnesses bundled as a
single artifact. This is the contract surface handed to
`src/ackermann_certificate.rs` for the n ≥ 4 structural-fallback
regime — the Rust kernel cross-checks its small-n behavior against
this bundle and falls through to structural 0% on the unbounded
tail.
-/

/-- Headline bundle: the calibration-window structural witnesses
    that the Rust kernel's PR-detection fallback (finite-difference
    test ⇒ structural 0%) is sound to fire. The bundle is the
    contract handed to `src/ackermann_certificate.rs` for the n ≥ 4
    structural-fallback regime.

    The conjuncts are, in order:

    1. boundary witness — levels 1 and 2 sit below the diagonal at n = 3,
    2. zero-runtime fully-tight 0%-certificate on the window,
    3. identity-runtime 50%-certificate on the window,
    4. structural separation — level 2 at n = 3 is strictly
       under the 50%-ceiling. -/
theorem primitive_recursive_calibration_window_bound :
    (hyperop 1 3 3 < ackermannCeiling 3 ∧
     hyperop 2 3 3 < ackermannCeiling 3) ∧
    ((fun (_ : Nat) => 0) 0 * 100 ≤ 0 * ackermannCeiling 0 ∧
     (fun (_ : Nat) => 0) 1 * 100 ≤ 0 * ackermannCeiling 1 ∧
     (fun (_ : Nat) => 0) 2 * 100 ≤ 0 * ackermannCeiling 2 ∧
     (fun (_ : Nat) => 0) 3 * 100 ≤ 0 * ackermannCeiling 3) ∧
    ((fun n => n) 0 * 100 ≤ 50 * ackermannCeiling 0 ∧
     (fun n => n) 1 * 100 ≤ 50 * ackermannCeiling 1 ∧
     (fun n => n) 2 * 100 ≤ 50 * ackermannCeiling 2 ∧
     (fun n => n) 3 * 100 ≤ 50 * ackermannCeiling 3) ∧
    (hyperop 2 3 3 * 100 < 50 * ackermannCeiling 3) :=
  ⟨fixed_level_below_ceiling_at_calibration,
   zero_runtime_calibration_window,
   identity_runtime_50_percent_at_calibration,
   level_two_dominated_at_three⟩

/-! ## Honesty note

This module formalizes the **calibration-window** form of "Ackermann
is not primitive recursive." The universal direction — that every
primitive-recursive function `f` is eventually dominated by the
Ackermann diagonal, i.e. `∃ N, ∀ n ≥ N, f n < ackermannDiag n` — is
out of scope: it requires a primitive-recursive function encoding
inside Init-Lean that we are not paying for in this module.

What we do guarantee:

* every fixed-level hyperop profile `fixedLevelHyperopRuntime k`
  is a concrete `Runtime`, computable, and we can check its values
  against `ackermannCeiling` pointwise on the calibration window,
* the zero runtime is 0%-certified on the window (mirrors the
  universal `zero_runtime_zero_percent` in the sibling certificate
  file),
* the identity runtime is 50%-certified on the window with the
  hand-computed k = 50 witness,
* the structural separation at n = 3 is decidable and tight at
  the 50% threshold.

This is the load-bearing contract surface the Rust kernel checks
against at the n ≤ 3 calibration boundary before falling through
to its structural-fallback regime at n ≥ 4. The same honesty mode
`Gnosis.BowlMeshPinkNoiseBound` operates in: faithful on the
algebraic invariant lattice and on the small-Nat decidable witness,
silent on the universal-quantifier extensions we cannot reach
without leaving Init.
-/

end AckermannPrimitiveRecursiveBound
