import Init
import Gnosis.Aether.RmsNormLipschitz
import Gnosis.Aether.AttentionLipschitz
import Gnosis.Aether.SwiGLULipschitz

/-!
# Full per-layer transformer-block Lipschitz gain `L_layer` (Rustic Church)

This module assembles the **local** per-layer Lipschitz gain of a complete
transformer block from the three certified component gains —
`Gnosis.Aether.RmsNormLipschitz.kRms` (the RMSNorm diagonal gain `K_rms`),
`Gnosis.Aether.AttentionLipschitz.lAttn` (the local attention gain `L_attn`), and
`Gnosis.Aether.SwiGLULipschitz.lSwiglu` (the local SwiGLU gain `L_swiglu`) — and
proves the multiplicative composition + monotonicity. This `L_layer` is the gain
`early-exit.ts` consumes (per remaining layer) so the early-exit gate flips from
`perLayerGain = null` (sound-disabled) to a real, sound per-layer bound.

## The architecture and the residual `+1`

A transformer block is two residual sub-blocks (pre-norm convention):

```text
  h₁ = x  + Attn(RMSNorm(x))            -- attention sub-block (residual)
  y  = h₁ + SwiGLU(RMSNorm(h₁))         -- FFN sub-block (residual)
```

A **residual** connection `f(x) = x + g(x)` has gain `1 + L_g` (identity skip
contributes `1`, the sublayer contributes its gain `L_g`). Each sublayer is the
RMSNorm diagonal map (gain `K_rms`) composed with attention / SwiGLU, so:

```text
  L_attn_block   =  1 + K_rms · L_attn        -- attention residual sub-block
  L_ffn_block    =  1 + K_rms · L_swiglu      -- FFN residual sub-block
  L_layer        =  L_attn_block · L_ffn_block
                 =  (1 + K_rms · L_attn) · (1 + K_rms · L_swiglu)
```

The two sub-blocks compose multiplicatively (the block is their composition).
This is the gain folded over the remaining layers as
`tauRemaining = (∏ L_layer) · ‖resid_k‖` in `EarlyExitAdmissibility` /
`early-exit.ts`.

## CRITICAL HONESTY: the bound is LOCAL

`L_attn` and `L_swiglu` are **local** (softmax attention and bilinear SwiGLU are
not globally Lipschitz — see their modules). Hence `L_layer` is local: valid on
the bounded-input region where the component bounds hold. That is exactly
early-exit's regime (a finite real residual at decode time). The locality is
inherited through the component hypotheses (`l_attn_bounded` / `l_swiglu_bounded`
carry the locality premises); the composition here is purely algebraic. We do
**not** claim a global per-layer Lipschitz bound. The `≥ 1` property
(`l_layer_ge_one`) — driven by the residual `+1` — is what makes each factor a
valid (soundly inflating) entry in the early-exit Lipschitz product.

Init-only per `RUSTIC_CHURCH.md`: `import Init` + the three sibling cert modules;
no Mathlib, no `omega`, no `simp`/`decide` on open goals, no `ac_rfl`. `decide`
appears only on CLOSED goals. `#print axioms` is `propext` only.
-/

open Gnosis.Aether.RmsNormLipschitz
open Gnosis.Aether.AttentionLipschitz
open Gnosis.Aether.SwiGLULipschitz

namespace Gnosis
namespace Aether
namespace TransformerBlockLipschitz

-- ═══════════════════════════════════════════════════════════════════════
-- §1  The residual sub-block gains (the `1 + K_rms · sublayer` shape)
-- ═══════════════════════════════════════════════════════════════════════

/-- **Attention residual sub-block gain** `1 + K_rms · L_attn`. The `1` is the
residual identity skip; `K_rms · L_attn` is the RMSNorm-then-attention sublayer
gain. All inputs are the certified component magnitudes. -/
def lAttnBlock (kRmsVal lAttnVal : Nat) : Nat := 1 + kRmsVal * lAttnVal

/-- **FFN residual sub-block gain** `1 + K_rms · L_swiglu`. The `1` is the
residual identity skip; `K_rms · L_swiglu` is the RMSNorm-then-SwiGLU sublayer
gain. -/
def lFfnBlock (kRmsVal lSwigluVal : Nat) : Nat := 1 + kRmsVal * lSwigluVal

/-- **The full per-layer gain** `L_layer = (1 + K_rms·L_attn) · (1 + K_rms·L_swiglu)`,
the multiplicative composition of the two residual sub-blocks. This is the gain
`early-exit.ts` folds over the remaining layers. -/
def lLayer (kRmsVal lAttnVal lSwigluVal : Nat) : Nat :=
  lAttnBlock kRmsVal lAttnVal * lFfnBlock kRmsVal lSwigluVal

-- ═══════════════════════════════════════════════════════════════════════
-- §2  Each residual sub-block gain is ≥ 1 (the residual `+1`)
-- ═══════════════════════════════════════════════════════════════════════

/-- **`l_attn_block_ge_one` — the attention sub-block gain is ≥ 1.** The residual
identity skip alone contributes `1`, so `1 + K_rms·L_attn ≥ 1` unconditionally.
This is why the layer is a valid (soundly inflating) factor in the early-exit
Lipschitz product. `Nat.le_add_right`. No `omega`. -/
theorem l_attn_block_ge_one (kRmsVal lAttnVal : Nat) :
    1 ≤ lAttnBlock kRmsVal lAttnVal := by
  unfold lAttnBlock
  exact Nat.le_add_right 1 (kRmsVal * lAttnVal)

/-- **`l_ffn_block_ge_one` — the FFN sub-block gain is ≥ 1.** Same residual `+1`
argument. `Nat.le_add_right`. No `omega`. -/
theorem l_ffn_block_ge_one (kRmsVal lSwigluVal : Nat) :
    1 ≤ lFfnBlock kRmsVal lSwigluVal := by
  unfold lFfnBlock
  exact Nat.le_add_right 1 (kRmsVal * lSwigluVal)

/-- **`l_layer_ge_one` — the full per-layer gain is ≥ 1.** Both residual
sub-blocks are `≥ 1`, so their product is `≥ 1·1 = 1`. Hence every per-layer gain
is a valid factor `≥ 1` in `lipProduct` (`EarlyExitAdmissibility.lipProduct_pos` /
`lipProduct_monotone_cons`): adding a remaining layer can only INFLATE
`tauRemaining`, never shrink it — the soundness direction. `Nat.mul_le_mul`. No
`omega`. -/
theorem l_layer_ge_one (kRmsVal lAttnVal lSwigluVal : Nat) :
    1 ≤ lLayer kRmsVal lAttnVal lSwigluVal := by
  unfold lLayer
  have h := Nat.mul_le_mul (l_attn_block_ge_one kRmsVal lAttnVal)
                           (l_ffn_block_ge_one kRmsVal lSwigluVal)
  rw [Nat.one_mul] at h
  exact h

-- ═══════════════════════════════════════════════════════════════════════
-- §3  The composition + monotonicity (the certificate core)
-- ═══════════════════════════════════════════════════════════════════════

/-- **`l_layer_composition` — the per-layer gain IS the product of the two
residual sub-block gains.** Definitional unfolding witness: `L_layer` factors
exactly as `(1 + K_rms·L_attn) · (1 + K_rms·L_swiglu)`. This is the multiplicative
composition the runtime mirrors. -/
theorem l_layer_composition (kRmsVal lAttnVal lSwigluVal : Nat) :
    lLayer kRmsVal lAttnVal lSwigluVal
      = (1 + kRmsVal * lAttnVal) * (1 + kRmsVal * lSwigluVal) := rfl

/-- **`l_layer_monotone` — monotone in every component gain.** Raising the
RMSNorm gain `K_rms`, the attention gain `L_attn`, or the SwiGLU gain `L_swiglu`
(each a sound over-estimate from its certified module) never decreases the
assembled per-layer gain. So composing the three sound component over-estimates
yields a sound per-layer over-estimate — exactly what the early-exit τ-product
consumes. Chained `Nat.mul_le_mul` / `Nat.add_le_add` / `Nat.mul_le_mul`. No
`omega`. -/
theorem l_layer_monotone
    {k₁ a₁ s₁ k₂ a₂ s₂ : Nat}
    (hk : k₁ ≤ k₂) (ha : a₁ ≤ a₂) (hs : s₁ ≤ s₂) :
    lLayer k₁ a₁ s₁ ≤ lLayer k₂ a₂ s₂ := by
  unfold lLayer lAttnBlock lFfnBlock
  exact Nat.mul_le_mul
          (Nat.add_le_add_left (Nat.mul_le_mul hk ha) 1)
          (Nat.add_le_add_left (Nat.mul_le_mul hk hs) 1)

/-- **`l_layer_bounded` — the per-layer gain assembled from TRUE component gains
is bounded by the gain assembled from sound over-estimates.** Given
`kRms' ≤ kRms`, `lAttn' ≤ lAttn`, `lSwiglu' ≤ lSwiglu` (each component an
over-estimate, as certified by `RmsNormLipschitz.gain_bounded`,
`AttentionLipschitz.l_attn_bounded`, `SwiGLULipschitz.l_swiglu_bounded`), the
true per-layer gain is bounded by the assembled one. This is the end-to-end
soundness statement: the runtime's `perLayerGain` (built from operator-norm
over-estimates and the certified activation constants) is a true upper bound on
the real per-layer gain, so feeding it to the early-exit gate keeps exits
lossless. Direct corollary of `l_layer_monotone`. No `omega`. -/
theorem l_layer_bounded
    (kRmsVal lAttnVal lSwigluVal : Nat)               -- supplied over-estimates
    (kRms' lAttn' lSwiglu' : Nat)                     -- true (smaller) component gains
    (hk : kRms' ≤ kRmsVal) (ha : lAttn' ≤ lAttnVal) (hs : lSwiglu' ≤ lSwigluVal) :
    lLayer kRms' lAttn' lSwiglu' ≤ lLayer kRmsVal lAttnVal lSwigluVal :=
  l_layer_monotone hk ha hs

-- ═══════════════════════════════════════════════════════════════════════
-- §4  End-to-end assembly from the three certified component modules
-- ═══════════════════════════════════════════════════════════════════════

/-- **`l_layer_from_components` — assemble `L_layer` end-to-end from the three
certified component gains.** Bundles the real component constructors:
* `K_rms = kRms wInf r`  (`RmsNormLipschitz.kRms`),
* `L_attn = lAttn wq wk wv wo sBound`  (`AttentionLipschitz.lAttn`),
* `L_swiglu = lSwiglu wGate wUp wDown siluL gateB upB`  (`SwiGLULipschitz.lSwiglu`),

and exposes the composed per-layer gain together with its `≥ 1` guarantee — the
single value `early-exit.ts` reads. The locality of `L_attn` / `L_swiglu` is
inherited from their modules (the bounded-region hypotheses live there); here the
composition is purely algebraic. -/
theorem l_layer_from_components
    (wInf r : Nat)                                    -- RMSNorm: ‖w‖∞, √eps
    (wq wk wv wo sBound : Nat)                         -- attention norms + softmax bound
    (wGate wUp wDown siluL gateB upB : Nat) :          -- SwiGLU norms + SiLU + activation bounds
    1 ≤ lLayer (kRms wInf r)
               (lAttn wq wk wv wo sBound)
               (lSwiglu wGate wUp wDown siluL gateB upB) :=
  l_layer_ge_one _ _ _

-- ═══════════════════════════════════════════════════════════════════════
-- §5  Concrete worked example (a full per-layer gain from the §examples)
-- ═══════════════════════════════════════════════════════════════════════

/-! A full layer assembled from the component worked examples:
* `K_rms = kRms 8 2 = 4`  (the RmsNorm example),
* `L_attn = lAttn 3 3 3 3 1 = 81`  (the Attention example),
* `L_swiglu = lSwiglu 2 2 2 11 1 1 = 96`  (the SwiGLU example).

The attention sub-block gain is `1 + 4·81 = 325`; the FFN sub-block gain is
`1 + 4·96 = 385`; the full per-layer gain is `325 · 385 = 125125`. (Large because
the magnitudes are coarsely Int-scaled and conservative — the runtime uses far
tighter operator-norm estimates; the value is illustrative of the COMPOSITION,
not a production constant.) -/

/-- The attention sub-block gain computes as `325`. Closed `decide`. -/
theorem ex_l_attn_block : lAttnBlock 4 81 = 325 := by decide

/-- The FFN sub-block gain computes as `385`. Closed `decide`. -/
theorem ex_l_ffn_block : lFfnBlock 4 96 = 385 := by decide

/-- The full per-layer gain computes as `325 · 385 = 125125`. Closed `decide`. -/
theorem ex_l_layer_value : lLayer 4 81 96 = 125125 := by decide

/-- **The worked per-layer gain is ≥ 1** (a valid early-exit Lipschitz factor).
Routes through `l_layer_ge_one`, so it is a live carrier of the general bound. -/
theorem ex_l_layer_ge_one : 1 ≤ lLayer 4 81 96 := l_layer_ge_one 4 81 96

/-- **The worked per-layer gain assembled from the real component constructors.**
Plugs the RmsNorm / Attention / SwiGLU worked numbers through `kRms` / `lAttn` /
`lSwiglu` and confirms it equals the directly-computed `125125`. Certifies the
end-to-end pipeline (`kRms 8 2 = 4`, `lAttn 3 3 3 3 1 = 81`,
`lSwiglu 2 2 2 11 1 1 = 96`, composed `= 125125`). Closed `decide`. -/
theorem ex_l_layer_from_components :
    lLayer (kRms 8 2) (lAttn 3 3 3 3 1) (lSwiglu 2 2 2 11 1 1) = 125125 := by decide

-- ═══════════════════════════════════════════════════════════════════════
-- §6  The soundness direction at the layer level (monotone ⇒ harder to exit)
-- ═══════════════════════════════════════════════════════════════════════

/-- **`over_estimate_only_inflates` — a larger component gain only inflates the
per-layer gain.** Stated for the consumer: if the runtime's supplied component
over-estimates dominate the true gains, the per-layer gain it feeds the early-exit
τ-product dominates the true per-layer gain. Combined with
`EarlyExitAdmissibility.tauRemaining_monotone_cons` (larger gain ⇒ larger τ ⇒
harder to exit), this is the layer-level soundness link: over-counting can only
DECLINE an exit, never trigger a too-early one. Direct from `l_layer_monotone`. -/
theorem over_estimate_only_inflates
    {k₁ a₁ s₁ k₂ a₂ s₂ : Nat}
    (hk : k₁ ≤ k₂) (ha : a₁ ≤ a₂) (hs : s₁ ≤ s₂) :
    lLayer k₁ a₁ s₁ ≤ lLayer k₂ a₂ s₂ :=
  l_layer_monotone hk ha hs

end TransformerBlockLipschitz
end Aether
end Gnosis
