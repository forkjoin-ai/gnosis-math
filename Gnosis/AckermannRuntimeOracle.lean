import Init
import Gnosis.AckermannFunction
import Gnosis.AckermannRuntimeCertificate

/-
  AckermannRuntimeOracle.lean
  ===========================

  Lean → Rust oracle theorems for the Ackermann runtime certification
  kernel.

  Mirrors the `vandermonde_runtime_oracle_*` block in
  `Gnosis.AmplituhedronFalsifiability` and the
  `bowl_mesh_runtime_oracle_pentad` block in
  `Gnosis.BowlMeshRuntimeOracle`: fixes the small family of canonical
  diagonal arguments whose `ackermannCeiling` value is the contract the
  Rust kernel (`src/ackermann_certificate.rs`) MUST reproduce. Any Rust
  drift from these values — or any failure to enter the structural
  fallback regime at `n = 4` — is a falsification of the parity
  contract.

  ## Why this is the load-bearing test surface

  The `AckermannFunction` module proves *structural* properties of the
  hyperoperation diagonal: `ack_0..ack_3`, growth, level-variation,
  dominance over fixed-level towers. The `AckermannRuntimeCertificate`
  module gives the `Runtime`, `ackermannCeiling`, and
  `IsKPercentCertified` scaffolding. Neither pins the specific numeric
  values that any Rust runtime executing `ackermann_ceiling(n)` MUST
  return. This module does.

  These five contracts are the actual Lean ↔ Rust agreement points.
  The first four are decidable in `Nat`; the fifth is the structural
  sentinel for the `n ≥ 4` regime where direct numeric reduction is
  infeasible — Rust returns `None` ("structural fallback regime
  entered"), Lean records the symbolic identity `ackermannCeiling 4 =
  hyperop 4 4 4`. Both sides describe the same regime by different
  means; this is the f32-mask-equivalent for unbounded arithmetic.

  Imports `Init` plus the upstream Ackermann function module and the
  runtime certificate scaffolding. Zero `sorry`, zero new `axiom`.
-/


namespace AckermannRuntimeOracle

open AckermannFunction
open AckermannRuntimeCertificate

/-! ## The pentad

Five Lean-Nat equalities the Rust kernel MUST reproduce. The first
four are decidable; the fifth is the structural sentinel for the
n ≥ 4 regime where direct numeric computation is infeasible. -/

/-- **Runtime contract #1.** `ackermannCeiling 0 = 1`. Rust
    `ackermann_ceiling(0)` MUST return `Some(1)`. -/
theorem ackermann_runtime_oracle_zero :
    ackermannCeiling 0 = 1 := by
  unfold ackermannCeiling; exact ack_0

/-- **Runtime contract #2.** `ackermannCeiling 1 = 2`. Rust
    `ackermann_ceiling(1)` MUST return `Some(2)`. -/
theorem ackermann_runtime_oracle_one :
    ackermannCeiling 1 = 2 := by
  unfold ackermannCeiling; exact ack_1

/-- **Runtime contract #3.** `ackermannCeiling 2 = 4`. Rust
    `ackermann_ceiling(2)` MUST return `Some(4)`. -/
theorem ackermann_runtime_oracle_two :
    ackermannCeiling 2 = 4 := by
  unfold ackermannCeiling; exact ack_2

/-- **Runtime contract #4.** `ackermannCeiling 3 = 27`. Rust
    `ackermann_ceiling(3)` MUST return `Some(27)`. -/
theorem ackermann_runtime_oracle_three :
    ackermannCeiling 3 = 27 := by
  unfold ackermannCeiling; exact ack_3

/-- **Runtime contract #5.** `ackermannCeiling 4 = hyperop 4 4 4`.
    This is the **structural sentinel**: the value is astronomically
    larger than any u64 can hold, so direct Nat arithmetic in Lean
    cannot reduce it via `decide`, and the Rust kernel cannot compute
    it either. The contract is that *the symbol* matches — Rust's
    `ackermann_ceiling(4)` MUST return `None` (i.e., "structural
    fallback regime entered"), and any Lean proof requiring this
    value must route through `hyperop 4 4 4` symbolically. -/
theorem ackermann_runtime_oracle_four_structural :
    ackermannCeiling 4 = hyperop 4 4 4 := by
  unfold ackermannCeiling ackermannDiag
  rfl

/-! ## Bundled witness

  A single statement that records all five runtime contracts
  together, matching the pattern of `bowl_mesh_runtime_oracle_pentad`
  in `BowlMeshRuntimeOracle` and `vandermonde_runtime_oracle_*` in
  `AmplituhedronFalsifiability`. The Rust side reproduces this exact
  pentad in `ackermann_certificate.rs::tests`. -/

/-- **Bundled pentad.** Single statement carrying all five oracle
    contracts; the Rust test surface in `ackermann_certificate.rs`
    will exercise this pentad point-for-point. -/
theorem ackermann_runtime_oracle_pentad :
    ackermannCeiling 0 = 1 ∧
    ackermannCeiling 1 = 2 ∧
    ackermannCeiling 2 = 4 ∧
    ackermannCeiling 3 = 27 ∧
    ackermannCeiling 4 = hyperop 4 4 4 :=
  ⟨ackermann_runtime_oracle_zero,
   ackermann_runtime_oracle_one,
   ackermann_runtime_oracle_two,
   ackermann_runtime_oracle_three,
   ackermann_runtime_oracle_four_structural⟩

end AckermannRuntimeOracle
