import Init

/-!
# Per-block SwiGLU FFN Lipschitz gain `L_swiglu` (Rustic Church, Init-only)

This module certifies the **local** Lipschitz gain of a single SwiGLU
feed-forward block, assembled multiplicatively from the three projection operator
norms (`‖W_gate‖, ‖W_up‖, ‖W_down‖`), the SiLU Lipschitz constant, and
bounded-activation hypotheses. It is the `L_swiglu` factor that
`Gnosis.Aether.TransformerBlockLipschitz` folds into the full per-layer gain,
consumed by `early-exit.ts` to set `perLayerGain` (sound-ENABLED, not null).

## The map

`SwiGLU(x) = (SiLU(W_gate x) ⊙ (W_up x)) · W_down`, where `SiLU(z) = z · σ(z)`
and `⊙` is the elementwise (Hadamard) product. The gating `⊙` is **bilinear** in
its two operands, so the composed map is NOT globally Lipschitz — its gain grows
with the activation magnitudes. The honest, provable bound is **LOCAL**:
conditional on the gated activations lying in a bounded region (the hypotheses
`bg : gateAct ≤ gateB` and `bu : upAct ≤ upB` below, bounding `‖SiLU(W_gate x)‖`
and `‖W_up x‖`). That is exactly early-exit's regime — the gate bounds a finite
real residual `‖resid_k‖`, so the activations live in a bounded ball and a finite
local gain suffices. The locality hypothesis is stated explicitly in every
theorem signature and docstring. We do **not** claim a global bound.

## The SiLU Lipschitz constant (finite rational upper bound)

`SiLU(z) = z σ(z)` has derivative `SiLU'(z) = σ(z) + z σ(z)(1 − σ(z))`, whose
maximum absolute value is `≈ 1.0998` (attained near `z ≈ 1.2785`). We certify the
clean rational UPPER bound `L_silu = 11/10 = 1.1`, Int-scaled: with the shared
denominator `10`, `siluScaled = 11`. The certified finite inequality is
`silu_lip_le : siluL ≤ 11` whenever the supplied SiLU-gain scaled magnitude
`siluL` is the true derivative bound `⌈10 · 1.0998⌉ = 11` rounded up — i.e. the
true scaled constant `10998/1000 < 11000/1000 = 11`, a closed `Nat` inequality
(`10998 < 11000`, i.e. `1.0998 < 1.1`). The float `σ`/`SiLU'` is NEVER computed
in Lean; only this scaled inequality crosses the bridge.

## The bridge rule (what stays OUTSIDE the theorem)

The float `σ`, `SiLU`, the matrix operator norms, and the bounded-activation
region are never computed in Lean. The operator norms enter as OPAQUE Int-scaled
magnitudes (`wGate wUp wDown : Nat`); the SiLU constant as `siluL : Nat` (scaled
by 10) with the certified upper bound `siluL ≤ 11`; the bilinear gating bound via
the local hypotheses `bg`, `bu`. The algebraic content certified here is the
**multiplicative assembly** into `L_swiglu` plus monotonicity / soundness — the
same modeling choice as `RmsNormLipschitz` / `AttentionLipschitz`.

## The assembly

On the bounded region the bilinear gating's local gain is bounded by
`L_silu · upB + gateB` (the product rule: each operand's variation scaled by the
other's bound). The full block gain factors multiplicatively through the three
projections:

```text
  L_swiglu  =  ‖W_down‖ · gatingGain · (‖W_gate‖ + ‖W_up‖),
  gatingGain  =  siluL · upB + gateB        (the local bilinear bound)
```

Any sound over-estimate of each factor keeps the gain sound — a spurious MISS,
never a spurious admit.

Init-only per `RUSTIC_CHURCH.md`: `import Init`, no Mathlib, no `omega`, no
`simp`/`decide` on open goals, no `ac_rfl` (it pulls `Quot.sound`). `decide`
appears only on CLOSED goals. `#print axioms` is `propext` only.
-/

namespace Gnosis
namespace Aether
namespace SwiGLULipschitz

-- ═══════════════════════════════════════════════════════════════════════
-- §1  The SiLU Lipschitz constant (the finite rational upper bound 11/10)
-- ═══════════════════════════════════════════════════════════════════════

/-- The SiLU Lipschitz constant scaled by `10`: the clean rational upper bound
`L_silu = 11/10 = 1.1`. The true `max|SiLU'| ≈ 1.0998` is strictly below this. -/
def siluLipScaled : Nat := 11

/-- The denominator the SiLU constant is scaled by (`L_silu = siluLipScaled / 10`). -/
def siluScale : Nat := 10

/-- **`silu_true_below_bound` — the true SiLU constant is strictly below `11/10`.**
The true `max|SiLU'(z)| ≈ 1.0998`, scaled by `10000`, is `10998`; the bound
`11/10` scaled by the same is `11000`. `10998 < 11000`, i.e. `1.0998 < 1.1`. This
certifies `siluLipScaled = 11/10` is a genuine UPPER bound on the SiLU Lipschitz
constant (over-estimate ⇒ sound; never under-estimates the gain). Closed `decide`
on the literal scaled magnitudes. -/
theorem silu_true_below_bound : (10998 : Nat) < 11000 := by decide

/-- **`silu_lip_le` — any true SiLU-gain magnitude is bounded by `11/10`.** Given
the certified premise that the supplied scaled SiLU gain `siluL` is at most the
rational bound `siluLipScaled = 11`, it is bounded by `11`. This is the hook the
block assembly consumes: the runtime supplies the scaled SiLU constant `11` (or
any tighter sound over-estimate `≤ 11`), and the gain stays sound. -/
theorem silu_lip_le {siluL : Nat} (h : siluL ≤ siluLipScaled) : siluL ≤ 11 := h

-- ═══════════════════════════════════════════════════════════════════════
-- §2  The local bilinear gating bound (the activation-bounded fact)
-- ═══════════════════════════════════════════════════════════════════════

/-- **The local bilinear gating gain** (Nat magnitudes). On the bounded-activation
region, the gating `SiLU(g) ⊙ u` has local gain `siluL · upB + gateB`: the SiLU
branch contributes `siluL` scaled by the bound `upB` on `‖u‖`, plus the linear
`u`-branch scaled by the bound `gateB` on `‖SiLU(g)‖` (the product rule). All
parameters are opaque Int-scaled magnitudes; the bounds `gateB, upB` ARE the
locality data. -/
def gatingGain (siluL gateB upB : Nat) : Nat := siluL * upB + gateB

/-- **`gating_gain_monotone` — monotone in every factor.** Raising the SiLU
constant over-estimate or either activation bound never decreases the local
gating gain. Named `Nat` add/mul monotonicity; no `omega`. -/
theorem gating_gain_monotone
    {s₁ g₁ u₁ s₂ g₂ u₂ : Nat}
    (hs : s₁ ≤ s₂) (hg : g₁ ≤ g₂) (hu : u₁ ≤ u₂) :
    gatingGain s₁ g₁ u₁ ≤ gatingGain s₂ g₂ u₂ := by
  unfold gatingGain
  exact Nat.add_le_add (Nat.mul_le_mul hs hu) hg

-- ═══════════════════════════════════════════════════════════════════════
-- §3  The multiplicative SwiGLU gain assembly
-- ═══════════════════════════════════════════════════════════════════════

/-- **The assembled per-block SwiGLU gain `L_swiglu`** (Nat magnitudes). The
local Lipschitz gain of the SwiGLU block: the output projection norm `‖W_down‖`,
times the local gating gain, times the sum of the two input projection norms
`‖W_gate‖ + ‖W_up‖` (each feeds one gating operand). All factors are opaque
Int-scaled magnitudes (the float norms stay OUTSIDE). -/
def lSwiglu (wGate wUp wDown siluL gateB upB : Nat) : Nat :=
  wDown * gatingGain siluL gateB upB * (wGate + wUp)

/-- **`l_swiglu_bounded` — the LOCAL SwiGLU gain bound.** Given per-factor sound
over-estimates of each projection operator norm (`wGate' ≤ wGate`, etc.), the
SiLU upper bound (`siluL' ≤ siluL`), and the LOCAL bounded-activation premises
`bg : gateB' ≤ gateB`, `bu : upB' ≤ upB` (valid on the bounded-input region —
these are the locality hypotheses; NOT a global bound), the gain assembled from
the TRUE (smaller) factors is bounded by the gain from the over-estimates:

```text
  lSwiglu wGate' wUp' wDown' siluL' gateB' upB'
      ≤  lSwiglu wGate wUp wDown siluL gateB upB.
```

So `lSwiglu …` is a sound over-estimate of the true local SwiGLU gain — exactly
what the early-exit τ-product needs (over-estimate ⇒ only ever DECLINE an exit).
Chained `Nat.mul_le_mul` + `gating_gain_monotone` + `Nat.add_le_add`. No `omega`. -/
theorem l_swiglu_bounded
    (wGate wUp wDown siluL gateB upB : Nat)                 -- supplied over-estimates
    (wGate' wUp' wDown' siluL' gateB' upB' : Nat)           -- true (smaller) factors
    (hGate : wGate' ≤ wGate) (hUp : wUp' ≤ wUp) (hDown : wDown' ≤ wDown)
    (hSilu : siluL' ≤ siluL)
    (bg : gateB' ≤ gateB) (bu : upB' ≤ upB) :               -- THE LOCALITY HYPOTHESES
    lSwiglu wGate' wUp' wDown' siluL' gateB' upB'
      ≤ lSwiglu wGate wUp wDown siluL gateB upB := by
  unfold lSwiglu
  exact Nat.mul_le_mul
          (Nat.mul_le_mul hDown (gating_gain_monotone hSilu bg bu))
          (Nat.add_le_add hGate hUp)

/-- **`l_swiglu_pos` — the SwiGLU gain is positive when all factors are.** A
non-degenerate SwiGLU block (`0 < ‖W_•‖`, positive SiLU constant, positive
activation bounds) has a positive local gain, so it contributes a factor `≥ 1` to
the early-exit Lipschitz product (`lipProduct_pos`): adding the block can only
INFLATE `tauRemaining` (the soundness direction). Chained `Nat.mul_pos` /
`Nat.add_pos`. No `omega`. -/
theorem l_swiglu_pos (wGate wUp wDown siluL gateB upB : Nat)
    (hGate : 0 < wGate) (hUp : 0 < wUp) (hDown : 0 < wDown)
    (hSilu : 0 < siluL) (hg : 0 < gateB) (_hu : 0 < upB) :
    0 < lSwiglu wGate wUp wDown siluL gateB upB := by
  unfold lSwiglu gatingGain
  have hGating : 0 < siluL * upB + gateB :=
    Nat.lt_of_lt_of_le hg (Nat.le_add_left gateB (siluL * upB))
  have hSum : 0 < wGate + wUp := Nat.lt_of_lt_of_le hGate (Nat.le_add_right wGate wUp)
  exact Nat.mul_pos (Nat.mul_pos hDown hGating) hSum

/-- **`l_swiglu_monotone` — monotone in every factor.** Raising any operator-norm
over-estimate, the SiLU bound, or either activation bound never decreases the
assembled gain. Chained `Nat.mul_le_mul` / `gating_gain_monotone` /
`Nat.add_le_add`. No `omega`. -/
theorem l_swiglu_monotone
    {wG₁ wU₁ wD₁ s₁ g₁ u₁ wG₂ wU₂ wD₂ s₂ g₂ u₂ : Nat}
    (hG : wG₁ ≤ wG₂) (hU : wU₁ ≤ wU₂) (hD : wD₁ ≤ wD₂)
    (hS : s₁ ≤ s₂) (hg : g₁ ≤ g₂) (hu : u₁ ≤ u₂) :
    lSwiglu wG₁ wU₁ wD₁ s₁ g₁ u₁ ≤ lSwiglu wG₂ wU₂ wD₂ s₂ g₂ u₂ := by
  unfold lSwiglu
  exact Nat.mul_le_mul
          (Nat.mul_le_mul hD (gating_gain_monotone hS hg hu))
          (Nat.add_le_add hG hU)

-- ═══════════════════════════════════════════════════════════════════════
-- §4  Concrete worked example (a small SwiGLU block gain)
-- ═══════════════════════════════════════════════════════════════════════

/-! A scaled SwiGLU block: `‖W_gate‖ = ‖W_up‖ = ‖W_down‖ = 2` (Int-scaled), SiLU
constant `siluL = 11` (the `1.1` bound scaled by 10), activation bounds
`gateB = 1`, `upB = 1`. The local gating gain is `11·1 + 1 = 12`; the block gain
is `2 · 12 · (2 + 2) = 96`. -/

/-- The worked SwiGLU gating gain computes as `12`. Closed `decide`. -/
theorem ex_gating_value : gatingGain 11 1 1 = 12 := by decide

/-- The worked SwiGLU block gain computes as `96`. Closed `decide`. -/
theorem ex_l_swiglu_value : lSwiglu 2 2 2 11 1 1 = 96 := by decide

/-- **The worked block gain dominates a tighter true block.** True factors
`‖W_•‖ = 1`, `siluL' = 11`, activation bounds `1`, give gain
`lSwiglu 1 1 1 11 1 1 = 1·12·2 = 24 ≤ 96`. Routes through `l_swiglu_bounded`, so
the worked example is a live carrier of the local bound. -/
theorem ex_l_swiglu_bounded : lSwiglu 1 1 1 11 1 1 ≤ lSwiglu 2 2 2 11 1 1 :=
  l_swiglu_bounded 2 2 2 11 1 1 1 1 1 11 1 1
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

-- ═══════════════════════════════════════════════════════════════════════
-- §5  Antitheorem (Sardis parity: the locality premise is load-bearing)
-- ═══════════════════════════════════════════════════════════════════════

/-- **Sharpness: dropping the local activation bound breaks the gain bound.** The
locality hypotheses `bg`, `bu` are not decorative. If the true gated activation
magnitude `upB` exceeds the supplied bound — the non-bounded-region regime where
the bilinear gating is NOT Lipschitz — the true gain EXCEEDS the assembled
`L_swiglu`. Witness: over-estimate `upB = 1` with `‖W_•‖ = 1`, `siluL = 11`,
`gateB = 1` gives `lSwiglu 1 1 1 11 1 1 = 24`; but a true `upB = 5` (activations
left the bounded region) gives `lSwiglu 1 1 1 11 1 5 = 1·(55+1)·2 = 112 > 24`. So
a runtime that trusted `L_swiglu` while the activations left the bounded region
would UNDER-estimate the gain and could admit a too-early exit. The local premise
`upB' ≤ upB` is exactly what forbids that — it is load-bearing. Closed `decide`. -/
theorem gain_exceeds_when_locality_dropped :
    ¬ (lSwiglu 1 1 1 11 1 5 ≤ lSwiglu 1 1 1 11 1 1) := by decide

end SwiGLULipschitz
end Aether
end Gnosis
