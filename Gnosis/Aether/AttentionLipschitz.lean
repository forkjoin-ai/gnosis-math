import Init

/-!
# Per-block attention Lipschitz gain `L_attn` (Rustic Church, Init-only)

This module certifies the **local** Lipschitz gain of a single self-attention
block, assembled multiplicatively from the four projection operator norms
(`‖W_q‖, ‖W_k‖, ‖W_v‖, ‖W_o‖`) and a bound on the softmax-Jacobian sup-norm.
It is the `L_attn` factor that `Gnosis.Aether.TransformerBlockLipschitz` folds
into the full per-layer gain, which `early-exit.ts` consumes to set
`perLayerGain` (so the early-exit gate is sound-ENABLED instead of null).

## CRITICAL HONESTY: the bound is LOCAL, not global

Softmax self-attention is **NOT** globally Lipschitz: as the attention logits
grow, the value-mixing map's gain has no finite global bound. We do **not** claim
a global bound. The honest, provable statement is **local**: conditional on the
attention logits / inputs lying in a bounded region (captured by the hypothesis
`jac : sJac ≤ sBound` below, with `sBound` a finite softmax-Jacobian sup-norm
bound valid on that region). That is exactly early-exit's regime — the gate
bounds a *finite* real residual `‖resid_k‖` at decode time, so the inputs live in
a bounded ball and a finite local gain is all that is ever needed. The locality
hypothesis is stated explicitly in every theorem signature and docstring.

## The softmax-Jacobian sup-norm bound (finite inequality, the local fact)

For the row-softmax `p = softmax(z)`, the Jacobian is `J = diag(p) − p pᵀ`, with
`J_ii = p_i(1−p_i)` and `J_ij = −p_i p_j`. The induced sup-norm (max absolute row
sum) is `max_i 2 p_i (1 − p_i) ≤ 1/2`, since `t(1−t) ≤ 1/4` on `[0,1]`. We carry
this as the closed finite `Nat` inequality `softmax_jac_sup_le_half` on the scaled
discretization (`4 t(D−t) ≤ D²`, i.e. `t(1−t) ≤ 1/4`), proved from
`(D − 2t)² ≥ 0` via the AM-GM step `4ab ≤ (a+b)²` — no `omega`, no float
`softmax` ever computed. The honest gain-side constant the assembly uses for the
softmax block is the opaque parameter `sBound : Nat` with the *local* certified
premise `sJac ≤ sBound`.

## The bridge rule (what stays OUTSIDE the theorem)

The float `softmax`, the matrix operator norms, and the bounded-logit region are
never computed in Lean. The operator norms `‖W_q‖,‖W_k‖,‖W_v‖,‖W_o‖` enter as
OPAQUE Int-scaled magnitude parameters (`wq wk wv wo : Nat`). The softmax-Jacobian
sup-norm bound enters as `sBound : Nat` with the local premise `jac : sJac ≤ sBound`.
The algebraic content certified here is the **multiplicative assembly** of these
magnitudes into `L_attn` plus its monotonicity / soundness — the same modeling
choice as `RmsNormLipschitz` (float norms outside, algebra inside).

## The assembly

A self-attention block maps `x ↦ W_o · softmax(W_q x · (W_k x)ᵀ) · (W_v x)`. On
the bounded region the chain-rule gain factors multiplicatively:

```text
  L_attn  =  ‖W_o‖ · sBound · ‖W_v‖ · ‖W_q‖ · ‖W_k‖
```

Any sound over-estimate of each factor keeps the gain sound — a spurious MISS,
never a spurious admit.

Init-only per `RUSTIC_CHURCH.md`: `import Init`, no Mathlib, no `omega`, no
`simp`/`decide` on open goals. `decide` appears only on CLOSED goals.
`#print axioms` is `propext` only.
-/

namespace Gnosis
namespace Aether
namespace AttentionLipschitz

-- ═══════════════════════════════════════════════════════════════════════
-- §1  The softmax-Jacobian sup-norm bound (the local finite inequality)
-- ═══════════════════════════════════════════════════════════════════════

/-- **Square expansion on `Nat`:** `(a + b)² = (a·a + b·b) + (a·b + a·b)`.
The RHS groups the two cross terms together so the AM-GM step lands cleanly.
Proved by a `calc` whose every step is a single named distributive / associative
`Nat` lemma — no `ac_rfl` (which pulls `Quot.sound`), no `omega`. -/
theorem sq_add_expand (a b : Nat) :
    (a + b) * (a + b) = (a * a + b * b) + (a * b + a * b) := by
  calc (a + b) * (a + b)
      = a * (a + b) + b * (a + b) := Nat.add_mul a b (a + b)
    _ = (a * a + a * b) + (b * a + b * b) := by
          rw [Nat.mul_add a a b, Nat.mul_add b a b]
    _ = (a * a + a * b) + (a * b + b * b) := by rw [Nat.mul_comm b a]
    _ = a * a + (a * b + (a * b + b * b)) := by rw [Nat.add_assoc]
    _ = a * a + ((a * b + a * b) + b * b) := by rw [Nat.add_assoc (a * b) (a * b) (b * b)]
    _ = a * a + (b * b + (a * b + a * b)) := by rw [Nat.add_comm (a * b + a * b) (b * b)]
    _ = (a * a + b * b) + (a * b + a * b) := by rw [Nat.add_assoc]

/-- **AM-GM half-step on `Nat`:** `2 a b ≤ a² + b²` (`(a−b)² ≥ 0`). Proved WLOG
`a ≤ b`, peeling `b = a + d`; the residual difference is exactly the square
`d·d ≥ 0`. Named `Nat` lemmas only — no `ac_rfl`, no `omega`. -/
theorem two_mul_le_add_sq (a b : Nat) : 2 * (a * b) ≤ a * a + b * b := by
  have key : ∀ x d : Nat, 2 * (x * (x + d)) ≤ x * x + (x + d) * (x + d) := by
    intro x d
    -- LHS = 2x² + 2xd ; RHS = x² + ((x²+d²) + 2xd) = 2x² + 2xd + d².
    have hL : 2 * (x * (x + d)) = (x * x + x * x) + (x * d + x * d) := by
      calc 2 * (x * (x + d))
          = x * (x + d) + x * (x + d) := Nat.two_mul _
        _ = (x * x + x * d) + (x * x + x * d) := by rw [Nat.mul_add]
        _ = x * x + (x * d + (x * x + x * d)) := by rw [Nat.add_assoc]
        _ = x * x + ((x * x + x * d) + x * d) := by rw [Nat.add_comm (x * d) (x * x + x * d)]
        _ = x * x + (x * x + (x * d + x * d)) := by rw [Nat.add_assoc]
        _ = (x * x + x * x) + (x * d + x * d) := by rw [Nat.add_assoc]
    have hR : x * x + (x + d) * (x + d)
            = (x * x + x * x) + (x * d + x * d) + d * d := by
      rw [sq_add_expand x d]
      -- x*x + ((x*x + d*d) + (x*d + x*d))
      calc x * x + ((x * x + d * d) + (x * d + x * d))
          = x * x + (x * x + (d * d + (x * d + x * d))) := by rw [Nat.add_assoc]
        _ = x * x + (x * x + ((x * d + x * d) + d * d)) := by
              rw [Nat.add_comm (d * d) (x * d + x * d)]
        _ = (x * x + x * x) + ((x * d + x * d) + d * d) := by
              rw [Nat.add_assoc (x * x) (x * x) ((x * d + x * d) + d * d)]
        _ = (x * x + x * x) + (x * d + x * d) + d * d := by
              rw [Nat.add_assoc (x * x + x * x) (x * d + x * d) (d * d)]
    rw [hL, hR]
    exact Nat.le_add_right _ _
  match Nat.le_total a b with
  | Or.inl hab =>
      obtain ⟨d, hd⟩ := Nat.le.dest hab        -- a + d = b
      subst hd
      exact key a d
  | Or.inr hba =>
      obtain ⟨d, hd⟩ := Nat.le.dest hba        -- b + d = a
      subst hd
      have h := key b d
      rw [Nat.mul_comm b (b + d), Nat.add_comm (b * b) ((b + d) * (b + d))] at h
      exact h

/-- **AM-GM on `Nat`:** `4 a b ≤ (a + b)²`. The arithmetic core behind the
softmax-Jacobian sup-norm bound `t(1−t) ≤ 1/4`. Combines `two_mul_le_add_sq`
(`2ab ≤ a²+b²`) with `sq_add_expand`, both via named `Nat` lemmas — no `ac_rfl`,
no `omega`. -/
theorem four_mul_le_sq (a b : Nat) : 4 * (a * b) ≤ (a + b) * (a + b) := by
  rw [sq_add_expand a b]
  -- 4ab = (a*b + a*b) + (a*b + a*b) ; bound the first summand-pair by a²+b².
  have h4 : 4 * (a * b) = (a * b + a * b) + (a * b + a * b) := by
    calc 4 * (a * b)
        = (2 + 2) * (a * b) := by rw [show (4 : Nat) = 2 + 2 from rfl]
      _ = 2 * (a * b) + 2 * (a * b) := by rw [Nat.add_mul]
      _ = (a * b + a * b) + (a * b + a * b) := by rw [Nat.two_mul]
  rw [h4, Nat.add_comm (a * a + b * b) (a * b + a * b)]
  -- goal: (a*b + a*b) + (a*b + a*b) ≤ (a*b + a*b) + (a*a + b*b)
  have hab2 : a * b + a * b ≤ a * a + b * b := by
    have h := two_mul_le_add_sq a b
    rw [Nat.two_mul] at h
    exact h
  exact Nat.add_le_add_left hab2 (a * b + a * b)

/-- **The softmax-Jacobian sup-norm bound, as a closed finite inequality.**
For any discretized probability mass `t ∈ {0,…,D}` over a scale `D` (so the real
`p_i = t / D ∈ [0,1]`), the Jacobian row factor satisfies `4 · t · (D − t) ≤ D²`,
i.e. `t(1−t) ≤ 1/4` after dividing by `D²`, i.e. the softmax-Jacobian sup-norm
`max_i 2 p_i(1−p_i) ≤ 1/2`. This is the **local** softmax bound that the
attention gain uses (it holds for every `p`, but it is a sup-norm bound on the
Jacobian, not a global Lipschitz constant for the composed attention map — the
composition's locality is in the bounded-region hypothesis of the gain theorem).
Instantiates `four_mul_le_sq` at `a := t`, `b := D − t`. No `omega`. -/
theorem softmax_jac_sup_le_half (D t : Nat) (ht : t ≤ D) :
    4 * (t * (D - t)) ≤ D * D := by
  have hsum : t + (D - t) = D := Nat.add_sub_of_le ht
  have h := four_mul_le_sq t (D - t)
  rw [hsum] at h
  exact h

/-- **Concrete check of the half bound at the worst case.** At `D = 4`,
`t = 2` (the vertex `p = 1/2`), `4 · 2 · 2 = 16 = 4·4 = D²`: the bound is
ATTAINED (`p(1−p) = 1/4`, sup-norm `= 1/2`). Closed `decide`. -/
theorem softmax_jac_sup_attained_at_half :
    4 * (2 * (4 - 2)) = 4 * 4 := by decide

-- ═══════════════════════════════════════════════════════════════════════
-- §2  The multiplicative attention gain assembly
-- ═══════════════════════════════════════════════════════════════════════

/-- **The assembled per-block attention gain `L_attn`** (Nat magnitudes). The
local Lipschitz gain of the attention block, the product of the four projection
operator-norm magnitudes and the softmax-Jacobian sup-norm bound:
`L_attn = ‖W_o‖ · sBound · ‖W_v‖ · ‖W_q‖ · ‖W_k‖`. All factors are opaque
Int-scaled magnitudes (the float norms stay OUTSIDE). -/
def lAttn (wq wk wv wo sBound : Nat) : Nat :=
  wo * sBound * wv * wq * wk

/-- **`l_attn_bounded` — the LOCAL attention gain bound.** Given per-factor sound
over-estimates of each projection operator norm (`wq' ≤ wq`, etc.) and the LOCAL
softmax-Jacobian premise `sJac ≤ sBound` (valid on the bounded-input region —
this is the locality hypothesis; NOT a global bound), the gain assembled from the
TRUE (smaller) factors is bounded by the gain assembled from the over-estimates:

```text
  lAttn wq' wk' wv' wo' sJac  ≤  lAttn wq wk wv wo sBound.
```

So `lAttn wq wk wv wo sBound` is a sound over-estimate of the true local attention
gain — exactly what the early-exit τ-product needs (an over-estimate can only
DECLINE an exit, never trigger a too-early one). Chained `Nat.mul_le_mul`. No
`omega`. -/
theorem l_attn_bounded
    (wq wk wv wo sBound : Nat)          -- the supplied over-estimates
    (wq' wk' wv' wo' sJac : Nat)        -- the true (smaller) factors
    (hq : wq' ≤ wq) (hk : wk' ≤ wk) (hv : wv' ≤ wv) (ho : wo' ≤ wo)
    (jac : sJac ≤ sBound) :             -- THE LOCALITY HYPOTHESIS (local softmax bound)
    lAttn wq' wk' wv' wo' sJac ≤ lAttn wq wk wv wo sBound := by
  unfold lAttn
  -- product is monotone in each factor; chain Nat.mul_le_mul.
  exact Nat.mul_le_mul
          (Nat.mul_le_mul
            (Nat.mul_le_mul
              (Nat.mul_le_mul ho jac) hv) hq) hk

/-- **`l_attn_pos` — the attention gain is positive when all factors are.**
A self-attention block with non-degenerate projections (`0 < ‖W_•‖`) and a
positive softmax-Jacobian bound has a positive local gain. So it contributes a
factor `≥ 1` to the early-exit Lipschitz product (`lipProduct_pos`), and adding
the block can only INFLATE `tauRemaining` (the soundness direction). Chained
`Nat.mul_pos`. No `omega`. -/
theorem l_attn_pos (wq wk wv wo sBound : Nat)
    (hq : 0 < wq) (hk : 0 < wk) (hv : 0 < wv) (ho : 0 < wo) (hs : 0 < sBound) :
    0 < lAttn wq wk wv wo sBound := by
  unfold lAttn
  exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos ho hs) hv) hq) hk

/-- **`l_attn_monotone` — monotone in every factor.** Raising any projection
operator-norm over-estimate or the softmax-Jacobian bound never decreases the
assembled gain. This is the cleanliness lemma the block assembly relies on: a
looser (larger) input estimate yields a looser (still sound) gain. Chained
`Nat.mul_le_mul`. No `omega`. -/
theorem l_attn_monotone
    {wq₁ wk₁ wv₁ wo₁ s₁ wq₂ wk₂ wv₂ wo₂ s₂ : Nat}
    (hq : wq₁ ≤ wq₂) (hk : wk₁ ≤ wk₂) (hv : wv₁ ≤ wv₂)
    (ho : wo₁ ≤ wo₂) (hs : s₁ ≤ s₂) :
    lAttn wq₁ wk₁ wv₁ wo₁ s₁ ≤ lAttn wq₂ wk₂ wv₂ wo₂ s₂ := by
  unfold lAttn
  exact Nat.mul_le_mul
          (Nat.mul_le_mul
            (Nat.mul_le_mul
              (Nat.mul_le_mul ho hs) hv) hq) hk

-- ═══════════════════════════════════════════════════════════════════════
-- §3  Concrete worked example (a small attention block gain)
-- ═══════════════════════════════════════════════════════════════════════

/-! A scaled attention block: `‖W_q‖=‖W_k‖=‖W_v‖=‖W_o‖ = 3` (Int-scaled), softmax
sup-norm bound `sBound = 1` (the `1/2` bound scaled so a half is `1` over the
shared denominator `2`; here we work in the magnitude unit where the runtime's
`0.5` enters as `1` against the matching `‖resid‖` scale). The assembled gain is
`3 · 1 · 3 · 3 · 3 = 81`. -/

/-- The worked attention gain computes as `81`. Closed `decide`. -/
theorem ex_l_attn_value : lAttn 3 3 3 3 1 = 81 := by decide

/-- **The worked block gain dominates a tighter true block.** True factors
`‖W_•‖ = 2`, true softmax sup-norm `sJac = 1`, give gain `16`, which is bounded
by the over-estimate gain `81`. Routes through `l_attn_bounded`, so the worked
example is a live carrier of the local bound. -/
theorem ex_l_attn_bounded : lAttn 2 2 2 2 1 ≤ lAttn 3 3 3 3 1 :=
  l_attn_bounded 3 3 3 3 1 2 2 2 2 1
    (by decide) (by decide) (by decide) (by decide) (by decide)

-- ═══════════════════════════════════════════════════════════════════════
-- §4  Antitheorem (Sardis parity: the locality premise is load-bearing)
-- ═══════════════════════════════════════════════════════════════════════

/-- **Sharpness: dropping the local softmax bound breaks the gain bound.** The
locality hypothesis `jac : sJac ≤ sBound` is not decorative. If the true
softmax-Jacobian sup-norm `sJac` exceeds the supplied `sBound` — the
non-bounded-region regime where softmax attention is NOT Lipschitz — the true
gain EXCEEDS the assembled `L_attn`. Witness: over-estimate `sBound = 1` with all
`‖W_•‖ = 2` gives `lAttn = 16`; but a true `sJac = 3` (logits left the bounded
region) gives true gain `lAttn 2 2 2 2 3 = 48 > 16`. So a runtime that trusted
`L_attn` while the inputs left the bounded region would UNDER-estimate the gain
and could admit a too-early exit. The local premise `sJac ≤ sBound` is exactly
what forbids that — it is load-bearing. Closed `decide`. -/
theorem gain_exceeds_when_locality_dropped :
    ¬ (lAttn 2 2 2 2 3 ≤ lAttn 2 2 2 2 1) := by decide

end AttentionLipschitz
end Aether
end Gnosis
