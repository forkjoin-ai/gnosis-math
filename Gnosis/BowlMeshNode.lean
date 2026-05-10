/-
  BowlMeshNode.lean
  =================

  Bowl-lifted mesh node: replaces the binary `standing_dims : List Nat`
  mask of `Gnosis.MeshStandingWavePinning.MeshNode` with a `TaoBowl` that
  damps off-resonance dimensions instead of zeroing them.

  ## Why this exists

  The 2026-05-03 falsification of the binary-mask pinning model
  (`open-source/gnosis/distributed-inference/`
   `STANDING_WAVE_STATUS_2026_05_03_AFTER_FALSIFICATION.md`) showed that a
  zero-fill mask on off-resonance dimensions corrupts the residual stream

      x_{l+1} = x_l + attn(x_l) + ffn(x_l)

  badly enough that on a 80-layer Llama-style probe the K=1 argmax decoded
  to position 0 / 79 — i.e. the network's prediction was destroyed at the
  first hop. The falsification names the failure mode: a binary mask is the
  wrong vessel because it removes the medium through which off-mode signal
  has to keep travelling.

  ## The reframe

  Daodejing 11 (formalized in `Gnosis.EchoChamberAsTaoBowl`) names the
  non-trivial half of vessel function: *void gives function*. A mesh node
  is a chamber; its dimensions are voices on the rim; off-resonance voices
  do not vanish, they ring quieter. The bowl couples to the signal through
  `filteredAmplitude` (`Gnosis.TaoBowlSignalCoupling`):

      on-mode:  amp * qFactor(bowl)
      off-mode: amp / (damping + 1)         -- damped, NOT zeroed.

  The binary-mask behavior is the limit of "infinite damping" — exactly
  the regime where the off-mode division crushes the signal to 0 in `Nat`.
  Outside that limit, off-mode dims keep contributing, the residual stream
  is preserved, and the layer stack stays well-conditioned.

  ## What's formalized here

  * `BowlMeshNode` — the structure that swaps `standing_dims` for `bowl`.
  * `route_through_bowl` — the bowl-lifted route function (just
    `filteredAmplitude` at the node's bowl).
  * `mask_at_high_damping` — large enough damping reproduces the binary
    mask's off-mode zero (the failure regime, made explicit).
  * `positive_damping_preserves_signal` — outside that regime, off-mode
    amplitude stays ≥ 1 whenever the input amplitude beats `damping + 1`.
    This is the structural property the binary mask violated.
  * `bowl_route_total_unlike_mask` — a concrete witness: a moderate bowl
    routes an off-resonance signal to a strictly positive amplitude, in
    direct contrast to the binary-mask zero-fill that motivated the
    falsification doc.

  Imports `Init` plus the two upstream bowl modules. Zero `sorry`, zero
  new `axiom`.
-/

import Init
import Gnosis.EchoChamberAsTaoBowl
import Gnosis.TaoBowlSignalCoupling

namespace BowlMeshNode

open EchoChamberAsTaoBowl
open TaoBowlSignalCoupling

/-- A mesh node whose dimension selectivity is a Tao bowl, not a binary
    mask. `fundamental_dim` records which dimension index is on-mode
    (matched against the bowl's `fundamentalMode`); `hidden_dim` is the
    full embedding width that the bowl filters into. -/
structure BowlMeshNode where
  node_id : Nat
  bowl : TaoBowl
  fundamental_dim : Nat
  hidden_dim : Nat
  deriving Repr

/-- The bowl-lifted route. Replaces
    `if dim ∈ standing_dims then amp else 0` with the bowl's coupled
    `filteredAmplitude`: on-resonance dims amplified by Q, off-resonance
    dims damped by `(damping + 1)`, never zeroed (in non-degenerate
    regimes — see `mask_at_high_damping` for the regime that does zero). -/
def route_through_bowl (n : BowlMeshNode) (freq amp : Nat) : Nat :=
  filteredAmplitude n.bowl freq amp

/-! ## The binary-mask regime is the high-damping limit

The current `MeshStandingWavePinning.MeshNode` zeroes off-resonance dims.
A bowl reproduces that exact behavior when `damping + 1 > amp`: Nat
division of `amp / (damping + 1)` is then `0`, matching the mask's
zero-fill. Naming this regime makes the failure mode legible — it is the
high-damping limit, not a different mechanism. -/

theorem mask_at_high_damping (n : BowlMeshNode) (freq amp : Nat)
    (hmiss : freqMismatch n.bowl freq ≠ 0)
    (hcrush : amp < n.bowl.damping + 1) :
    route_through_bowl n freq amp = 0 := by
  unfold route_through_bowl filteredAmplitude
  rw [if_neg hmiss]
  exact Nat.div_eq_of_lt hcrush

/-! ## Off-resonance amplitude survives in non-degenerate regimes

The structural property the binary mask violated: if the damping is not
in the crushing regime — equivalently, if the input amplitude clears the
`damping + 1` floor — then off-resonance routing returns a strictly
positive amplitude. This is what keeps the residual stream

    x_{l+1} = x_l + attn(x_l) + ffn(x_l)

from collapsing under the bowl, where it did collapse under the mask. -/

theorem positive_damping_preserves_signal (n : BowlMeshNode) (freq amp : Nat)
    (hmiss : freqMismatch n.bowl freq ≠ 0)
    (hamp : n.bowl.damping + 1 ≤ amp) :
    0 < route_through_bowl n freq amp := by
  unfold route_through_bowl filteredAmplitude
  rw [if_neg hmiss]
  have hpos : 0 < n.bowl.damping + 1 := Nat.succ_pos _
  have hone : 1 ≤ amp / (n.bowl.damping + 1) := by
    rw [Nat.le_div_iff_mul_le hpos]
    simpa using hamp
  exact Nat.lt_of_succ_le hone

/-! ## A concrete bowl-routed off-resonance signal is non-zero

The mask zero-fills every off-resonance dim. The bowl, at the same
off-resonance dim with a moderate damping, returns a positive amplitude.
The witness uses the upstream `balancedBowl` (damping = 1) and an
amplitude (100) well above the `damping + 1 = 2` floor. -/

def balancedBowlNode : BowlMeshNode where
  node_id := 0
  bowl := balancedBowl
  fundamental_dim := 3
  hidden_dim := 8

theorem bowl_route_total_unlike_mask :
    0 < route_through_bowl balancedBowlNode 10 100 := by
  unfold route_through_bowl filteredAmplitude balancedBowlNode
  decide

end BowlMeshNode
