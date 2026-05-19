import Init
import Gnosis.EchoChamberAsTaoBowl
import Gnosis.TaoBowlSignalCoupling
import Gnosis.BowlMeshNode

/-
  BowlMeshRuntimeOracle.lean
  ==========================

  Lean → Rust oracle theorems for the bowl-mesh Q-filter primitive.

  Mirrors the `vandermonde_runtime_oracle_*` block in
  `Gnosis.AmplituhedronFalsifiability` (the amplituhedron-side equivalent):
  fixes a small family of canonical bowls + canonical inputs whose
  `filteredAmplitude` value is computed in `Nat` by `decide`, then re-states
  the value as a contract the Rust kernel (`src/bowl_mesh.rs`,
  `BowlMeshHead`) MUST reproduce. Any Rust drift from these values is wrong.

  ## Why this is the load-bearing test surface

  The `BowlMeshNode` / `BowlMeshQSweep` modules prove structural properties:
  *that* the bowl preserves positivity off-resonance, *that* damping is
  monotone, *that* the binary mask is the high-damping regime
  (`BowlMeshNode.mask_at_high_damping`). They do **not** pin specific
  numeric values the Rust runtime must reproduce. This module does.

  These five contracts are the actual Lean ↔ Rust agreement points. The
  Rust unit tests in `src/bowl_mesh.rs` exercise the same witnesses; any
  divergence between the two sides is a falsification of the parity
  contract, not of the bowl model itself.

  Imports `Init` plus the upstream bowl module and the bowl-mesh node
  layer. Zero `sorry`, zero new `axiom`.
-/


namespace BowlMeshRuntimeOracle

open EchoChamberAsTaoBowl
open TaoBowlSignalCoupling
open BowlMeshNode

/-! ## On-resonance amplification

  `balancedBowl` has `rim = 5, void = 5, rigidity = 3, damping = 1`.
  `fundamentalMode = (5 * 3) / 5 = 3`. On-resonance, `filteredAmplitude`
  returns `amp * qFactor`. `qFactor = (5 * 3) / 1 = 15`. At `amp = 10`,
  the on-resonance output is `10 * 15 = 150`. -/

/-- **Runtime contract #1.** `balancedBowl` at `freq = 3` (= fundamental
    mode), `amp = 10` produces `150`. The Rust `BowlMeshHead::q_filter`
    on `(amp = 10.0, freq_idx = 3)` MUST produce `150.0` (within f32
    rounding, which is zero here — `10 * 15` is exactly representable). -/
theorem balancedBowl_runtime_oracle_on_resonance :
    filteredAmplitude balancedBowl 3 10 = 150 := by
  unfold filteredAmplitude balancedBowl freqMismatch fundamentalMode qFactor
  decide

/-! ## Off-resonance damping

  Same `balancedBowl`. At `freq = 7`, the mismatch is `|7 - 3| = 4 ≠ 0`,
  so `filteredAmplitude` takes the damped branch: `amp / (damping + 1) =
  10 / 2 = 5`. -/

/-- **Runtime contract #2.** `balancedBowl` at `freq = 7` (off mode),
    `amp = 10` produces `5`. Rust `BowlMeshHead::q_filter` on `(10.0, 7)`
    MUST produce `5.0` (exact in f32). The structural point: the output
    is non-zero — the residual stream survives the filter. -/
theorem balancedBowl_runtime_oracle_off_resonance :
    filteredAmplitude balancedBowl 7 10 = 5 := by
  unfold filteredAmplitude balancedBowl freqMismatch fundamentalMode
  decide

/-! ## High-damping mask regime

  A bowl with `damping = 99` and `amp = 10` enters the high-damping
  crushing regime (`amp < damping + 1`). Nat division of `10 / 100`
  returns `0`. This is the binary-mask-equivalent regime that
  `BowlMeshNode.mask_at_high_damping` names structurally.

  Rust f32 cannot return exact zero from `10.0 / 100.0` — it returns
  `0.1`. The Lean theorem captures the Nat truncation limit; the Rust
  runtime captures a "vanishing fraction" that, downstream of any
  normalization-aware comparison, behaves as zero relative to the
  on-resonance amplitudes. The qualitative claim is shared; the
  quantitative exactness differs by arithmetic. -/

/-- The high-damping bowl: same rim/void/rigidity as `balancedBowl`,
    but damping inflated past the mask threshold for `amp = 10`. -/
def highDampingBowl : TaoBowl :=
  { rim := 5, void := 5, rigidity := 3, damping := 99 }

/-- **Runtime contract #3.** `highDampingBowl` at `freq = 7` (off
    mode), `amp = 10` produces `0` in Nat — the binary-mask analogue.
    The Rust kernel's f32 path returns `0.1` for the same inputs; that
    is the documented arithmetic gap, not a contract violation. The
    contract is: in Nat / quantized arithmetic, the output is exactly
    zero, and in f32 it is below any normalization-relevant threshold. -/
theorem highDamping_runtime_oracle_mask_regime :
    filteredAmplitude highDampingBowl 7 10 = 0 := by
  unfold filteredAmplitude highDampingBowl freqMismatch fundamentalMode
  decide

/-! ## Pejorative-echo Q

  `pejorativeBowl` has `rim = 10, void = 2, rigidity = 100, damping = 1`.
  `qFactor = (10 * 100) / 1 = 1000`. This crosses the `IsPejorativeEcho`
  threshold (`Q ≥ 100`). -/

/-- **Runtime contract #4.** `pejorativeBowl`'s Q factor is exactly
    `1000`. Rust `BowlMeshHead::q_factor()` on the same constants MUST
    produce `1000`. The `is_pejorative_echo()` predicate must return
    `true` at this Q. -/
theorem pejorativeBowl_runtime_oracle_q_factor :
    qFactor pejorativeBowl = 1000 := by
  unfold qFactor pejorativeBowl
  decide

/-! ## Filled-bowl no-mode sentinel

  `filledBowl` has `void = 0`. `fundamentalMode` short-circuits to `0`
  (no void → no resonant mode), and `IsFilledBowl` holds. The bowl is
  dead by `filled_bowl_dead`. -/

/-- **Runtime contract #5.** `filledBowl.fundamentalMode = 0`. Rust
    `BowlMeshHead::fundamental_mode()` on `(5, 0, 3, 1, ...)` MUST
    return `0`, and `is_filled_bowl()` MUST return `true`. This is the
    no-mode sentinel: a Rust kernel that returns a nonzero fundamental
    for a void = 0 bowl is wrong. -/
theorem filledBowl_runtime_oracle_no_mode :
    fundamentalMode filledBowl = 0 := by
  unfold fundamentalMode filledBowl
  decide

/-! ## Bundled witness

  A single statement that records all five runtime contracts together,
  matching the pattern of `vandermonde_runtime_oracle_*` in
  `AmplituhedronFalsifiability`. The Rust side reproduces this exact
  pentad in `bowl_mesh.rs::tests`. -/

theorem bowl_mesh_runtime_oracle_pentad :
    filteredAmplitude balancedBowl 3 10 = 150 ∧
    filteredAmplitude balancedBowl 7 10 = 5 ∧
    filteredAmplitude highDampingBowl 7 10 = 0 ∧
    qFactor pejorativeBowl = 1000 ∧
    fundamentalMode filledBowl = 0 :=
  ⟨balancedBowl_runtime_oracle_on_resonance,
   balancedBowl_runtime_oracle_off_resonance,
   highDamping_runtime_oracle_mask_regime,
   pejorativeBowl_runtime_oracle_q_factor,
   filledBowl_runtime_oracle_no_mode⟩

end BowlMeshRuntimeOracle
