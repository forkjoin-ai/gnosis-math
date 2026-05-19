import Init
import Gnosis.EchoChamberAsTaoBowl
import Gnosis.TaoBowlSignalCoupling
import Gnosis.BowlMeshNode

/-
  BowlMeshQSweep.lean
  ===================

  The damping sweep companion to `Gnosis.BowlMeshNode`.

  ## Why this file exists

  The 2026-05-03 falsification of the binary-mask pinning model
  (`open-source/gnosis/distributed-inference/`
   `STANDING_WAVE_STATUS_2026_05_03_AFTER_FALSIFICATION.md`) showed that
  zero-filling off-resonance dims breaks the residual stream

      x_{l+1} = x_l + attn(x_l) + ffn(x_l)

  The bowl reframe (`Gnosis.BowlMeshNode`) replaces the zero-fill with the
  damped `filteredAmplitude` branch. The remaining knob is the bowl's
  `damping` field — the experimental sweep over which determines whether
  off-resonance contributions are crushed (high damping limit, recovers the
  failed mask) or kept proportional (low damping, keeps the residual
  stream intact).

  ## What's formalized here

  * `damping_sweep : List Nat` — the discrete sweep
    `[0, 1, 2, 4, 8, 16]` used by the K=1 acceptance experiments.
  * `bowl_at_damping` — build a bowl with rim/void/rigidity fixed and
    damping swept.
  * `off_resonance_strictly_positive` — for any bowl with
    `amp ≥ damping + 1`, the off-resonance filtered amplitude is at
    least 1 (the structural property the binary mask violated).
  * `damping_zero_off_resonance_pass_through` — at `damping = 0` the
    off-resonance branch is the identity (`amp / 1 = amp`); the bowl
    provides amplification on resonance but no attenuation off it. This
    is the degenerate "Q-amplifier-only" mode at the bottom of the
    sweep — distinct from (and less destructive than) the binary mask.
  * `high_damping_monotone_decay` — holding rim, void, rigidity fixed,
    raising damping monotonically lowers the off-resonance amplitude.
    Used by the sweep to detect a plateau where further damping stops
    helping K=1 argmax.
  * `layer_residual_nonzero_under_positive_damping` — list-level
    structural claim: under positive damping with `amp ≥ damping + 1`,
    every node in a layer routes an off-resonance signal to a strictly
    positive amplitude. This is exactly the property the binary mask
    falsified at layer 1 in the 80-layer probe.

  Imports `Init` plus the upstream bowl modules and the companion
  `Gnosis.BowlMeshNode`. Zero `sorry`, zero new `axiom`.
-/


namespace BowlMeshQSweep

open EchoChamberAsTaoBowl
open TaoBowlSignalCoupling
open BowlMeshNode

/-! ## The sweep -/

/-- A discrete damping sweep is a list of damping values to evaluate.
    These are the values the K=1 acceptance experiments sweep over: the
    bottom (`0`) recovers the Q-amplifier-only degenerate mode, and the
    top (`16`) approaches the crushing high-damping limit on the
    moderate-amplitude inputs the layer stack actually carries. -/
def damping_sweep : List Nat := [0, 1, 2, 4, 8, 16]

/-- Build a bowl with `rim`, `void`, `rigidity` fixed and `damping`
    swept. Used to materialize the sweep as a list of bowls sharing the
    same fundamental mode. -/
def bowl_at_damping (rim void rigidity damping : Nat) : TaoBowl :=
  { rim := rim, void := void, rigidity := rigidity, damping := damping }

/-! ## Off-resonance amplitude survives the sweep -/

/-- **Key theorem.** Off-resonance routing returns a filtered amplitude
    of at least `1` whenever the input amplitude clears the `damping + 1`
    floor.

    For an off-resonance signal, `filteredAmplitude b f amp = amp /
    (damping + 1)`. In `Nat`, this is `≥ 1` exactly when `amp ≥ damping
    + 1`. The structural content is that the bowl never zero-fills
    outside its high-damping crushing regime — the property the binary
    mask falsified at the very first layer of the 80-layer probe. -/
theorem off_resonance_strictly_positive (b : TaoBowl) (freq amp : Nat)
    (h_mismatch : freqMismatch b freq ≠ 0)
    (h_amp : amp ≥ b.damping + 1) :
    filteredAmplitude b freq amp ≥ 1 := by
  unfold filteredAmplitude
  rw [if_neg h_mismatch]
  have hpos : 0 < b.damping + 1 := Nat.succ_pos _
  show 1 ≤ amp / (b.damping + 1)
  rw [Nat.le_div_iff_mul_le hpos]
  simpa using h_amp

/-! ## Damping = 0 is the Q-amplifier-only degenerate mode -/

/-- **Damping zero is pass-through off-resonance.** At `damping = 0`,
    the off-resonance branch returns `amp / 1 = amp`: the bowl provides
    no attenuation. On-resonance the bowl still amplifies by `qFactor`,
    which is itself pinned to 0 at damping = 0 (`EchoChamberAsTaoBowl.
    qFactor_eq_zero_of_damping_eq_zero`), so the degenerate sweep
    bottom is "off-resonance preserved, on-resonance amplified-by-0".

    This is NOT the binary mask — the mask zero-fills off-resonance,
    crushing the residual stream. Damping = 0 keeps off-resonance amp
    intact and only collapses the on-resonance gain, which is the
    opposite failure mode. -/
theorem damping_zero_off_resonance_pass_through (b : TaoBowl)
    (h : b.damping = 0) (freq amp : Nat)
    (h_mismatch : freqMismatch b freq ≠ 0) :
    filteredAmplitude b freq amp = amp := by
  unfold filteredAmplitude
  rw [if_neg h_mismatch, h]
  show amp / (0 + 1) = amp
  rw [Nat.zero_add, Nat.div_one]

/-! ## Monotone decay across the sweep -/

/-- **High damping over-attenuates monotonically.** Hold rim, void,
    rigidity fixed; raise damping. Because `freqMismatch` depends only
    on `rim`, `void`, `rigidity` (via `fundamentalMode`), the
    off-resonance branch is taken for both bowls under the same
    mismatch hypothesis, and the result reduces to
    `amp / (b2.damping + 1) ≤ amp / (b1.damping + 1)`.

    Operationally, this is what the sweep uses to detect the plateau:
    once raising `damping` stops improving the K=1 argmax, further
    damping is just over-attenuating the off-resonance contribution
    and the sweep should stop. -/
theorem high_damping_monotone_decay (b1 b2 : TaoBowl) (freq amp : Nat)
    (h_mismatch1 : freqMismatch b1 freq ≠ 0)
    (h_mismatch2 : freqMismatch b2 freq ≠ 0)
    (h_eq : b1.rim = b2.rim ∧ b1.void = b2.void ∧ b1.rigidity = b2.rigidity)
    (h_damp : b1.damping ≤ b2.damping) :
    filteredAmplitude b2 freq amp ≤ filteredAmplitude b1 freq amp := by
  -- `h_eq` is documentary: under shared rim/void/rigidity the two bowls
  -- have the same `fundamentalMode`, hence the same `freqMismatch` for
  -- every `freq`. The proof itself rides on the off-resonance branch,
  -- which depends only on `damping`.
  have _doc := h_eq
  unfold filteredAmplitude
  rw [if_neg h_mismatch1, if_neg h_mismatch2]
  have hpos1 : 0 < b1.damping + 1 := Nat.succ_pos _
  have hle : b1.damping + 1 ≤ b2.damping + 1 := Nat.add_le_add_right h_damp 1
  exact Nat.div_le_div_left hle hpos1

/-! ## Layer-level residual preservation -/

/-- **Residual-stream preservation at the layer level.** If every node
    in a layer has `damping ≥ 1` and the input amplitude clears each
    node's `damping + 1` floor, then every node routes an off-resonance
    signal to a strictly positive amplitude.

    Statement is narrowed from "non-zero everywhere the input was
    non-zero" to the per-node positivity claim — the residual-stream
    add `x_{l+1} = x_l + attn(x_l) + ffn(x_l)` then inherits positivity
    componentwise. We do not commit to a particular aggregation across
    nodes (sum / max / merge) here; the load-bearing content is that no
    node zeroes the off-resonance contribution, which is exactly what
    the binary mask did and what falsified at layer 1 in the 80-layer
    probe. -/
theorem layer_residual_nonzero_under_positive_damping
    (nodes : List BowlMeshNode) (freq amp : Nat)
    (h_pos : ∀ n ∈ nodes, n.bowl.damping ≥ 1)
    (h_miss : ∀ n ∈ nodes, freqMismatch n.bowl freq ≠ 0)
    (h_amp : ∀ n ∈ nodes, amp ≥ n.bowl.damping + 1) :
    ∀ n ∈ nodes, 0 < route_through_bowl n freq amp := by
  intro n hn
  have hmiss := h_miss n hn
  have hamp := h_amp n hn
  -- `h_pos` is the structural witness that we are outside the
  -- damping = 0 degenerate mode; the positivity below does not need it
  -- directly because `damping + 1 ≥ 1` always, but the hypothesis
  -- documents the regime the layer is in.
  have _hpos := h_pos n hn
  exact positive_damping_preserves_signal n freq amp hmiss hamp

/-! ## Sweep witnesses

A concrete check that the sweep produces bowls that behave as the
theorems above predict on a moderate off-resonance input. The witnesses
fix `rim = 5, void = 5, rigidity = 3` (the upstream `balancedBowl`
parameters minus damping) and walk the sweep at `freq = 10, amp = 100`.
-/

/-- Damping = 0 bowl from the sweep: off-resonance pass-through. -/
theorem sweep_damping_zero_pass_through :
    filteredAmplitude (bowl_at_damping 5 5 3 0) 10 100 = 100 := by
  unfold filteredAmplitude bowl_at_damping freqMismatch fundamentalMode
  decide

/-- Damping = 1 bowl from the sweep: off-resonance survives at amp ≥ 1. -/
theorem sweep_damping_one_survives :
    filteredAmplitude (bowl_at_damping 5 5 3 1) 10 100 ≥ 1 :=
  off_resonance_strictly_positive (bowl_at_damping 5 5 3 1) 10 100
    (by unfold freqMismatch fundamentalMode bowl_at_damping; decide)
    (by decide)

/-- The sweep is monotone: the damping-16 bowl attenuates at least as
    much as the damping-1 bowl on the same off-resonance input. -/
theorem sweep_monotone_one_to_sixteen :
    filteredAmplitude (bowl_at_damping 5 5 3 16) 10 100
      ≤ filteredAmplitude (bowl_at_damping 5 5 3 1) 10 100 := by
  apply high_damping_monotone_decay
  · unfold freqMismatch fundamentalMode bowl_at_damping; decide
  · unfold freqMismatch fundamentalMode bowl_at_damping; decide
  · exact ⟨rfl, rfl, rfl⟩
  · decide

end BowlMeshQSweep
