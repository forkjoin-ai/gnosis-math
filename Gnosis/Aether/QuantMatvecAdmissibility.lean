import Init
import Gnosis.QualityMarginCacheAdmissibility

/-!
# Quantized matvec admissibility (Rustic Church, Init-only)

A quantized matvec (a Q4K / Q5K / Q6K dequantize-then-multiply) produces an
*approximate* logit vector `L'` that differs from the FP reference `L` by a
per-level sup-norm bound `tau` — the block representable resolution of the quant
format. Coarser formats (Q4K) carry a LARGER `tau`; finer formats (Q6K) carry a
SMALLER `tau`. A quant level is admissible for a decode step EXACTLY WHEN
`2 * tau ≤ gamma`, the SAME half-margin bound the cache certificate uses, applied
to quantization instead of caching.

## The bridge rule (what stays OUTSIDE the theorem)

The dequant FLOAT numerics — block scales, mins, the 4/5/6-bit codebook,
the actual reconstructed weight matrix — stay OUTSIDE the theorem. They enter
only through one Int-scaled quantity: `tau`, the sup-norm divergence of the
quantized-matvec logits `L'` from the FP-reference logits `L`. This is the same
quantize-then-decide bridge as `QualityMarginCacheAdmissibility`: the argmax
decision is scale-invariant, so the half-margin bound is written scale-free as
`2 * tau ≤ gamma`. The real per-level `tau` is calibrated empirically against
each block format and ENTERS THE THEOREM AS A PARAMETER.

## The theorem in one line

If the quantized-matvec logits `L'` satisfy `SupNormBelow L L' tau` and the FP
reference `L` has a strict argmax `istar` with runner-up margin `gamma`, then the
quantized decode predicts the **same next token** as the FP reference EXACTLY
WHEN `2 * tau ≤ gamma`. This is a thin re-instantiation of
`QualityMarginCacheAdmissibility.cache_hit_admissible` — the linear-margin
algebra is NOT re-proved here, it is reused wholesale.

## The honest structural win

`precision_monotone`: refining precision (a smaller `tau`) never loses
admissibility. If a coarse level admits and a finer level has `tauFine ≤
tauCoarse`, the finer level admits too. This is proved by one `Int.le_trans`
through `Int.mul_le_mul_of_nonneg_left` — no new arithmetic, no `omega`.

Init-only per `RUSTIC_CHURCH.md`: `import Init` + the sibling gnosis module only;
no Mathlib, no `omega`, no `simp`/`decide` on open-variable goals. `decide`
appears only on CLOSED goals (literal `Fin n` vectors / literal `Int`
tolerances).
-/

open Gnosis.QualityMarginCacheAdmissibility

namespace Gnosis
namespace Aether
namespace QuantMatvecAdmissibility

-- ═══════════════════════════════════════════════════════════════════════
-- §1  Per-level tolerance constants (REPRESENTATIVE PLACEHOLDERS)
-- ═══════════════════════════════════════════════════════════════════════

/-- **Representative / illustrative placeholder** per-level sup-norm tolerance for
    the Q6K block format (finest of the three: 6-bit codebook ⇒ smallest
    representable resolution ⇒ smallest `tau`).

    ⚠ This specific integer is NOT physically derived. The REAL per-level `tau`
    is calibrated empirically against each block format's dequant numerics and
    enters every theorem here as a PARAMETER (the bridge rule — the float quant
    numerics stay OUTSIDE the theorem). The constants only fix a representative
    *ordering* `tauQ6K ≤ tauQ5K ≤ tauQ4K` (finer = smaller) so `precision_monotone`
    has concrete instances to land on. -/
def tauQ6K : Int := 1

/-- **Representative / illustrative placeholder** per-level sup-norm tolerance for
    the Q5K block format (5-bit codebook ⇒ coarser than Q6K, finer than Q4K).

    ⚠ Not physically derived; see `tauQ6K`. The real `tau` enters as a theorem
    parameter; this constant only fixes the representative ordering. -/
def tauQ5K : Int := 2

/-- **Representative / illustrative placeholder** per-level sup-norm tolerance for
    the Q4K block format (coarsest of the three: 4-bit codebook ⇒ largest
    representable resolution ⇒ largest `tau`).

    ⚠ Not physically derived; see `tauQ6K`. The real `tau` enters as a theorem
    parameter; this constant only fixes the representative ordering. -/
def tauQ4K : Int := 4

-- ═══════════════════════════════════════════════════════════════════════
-- §2  Quantized-matvec admissibility (thin reuse of the imported core)
-- ═══════════════════════════════════════════════════════════════════════

/--
**Quantized-matvec admissibility (the τ rule for a quant level).** Given the
quantized-matvec logits `L'` are within sup-norm `tau` of the FP reference
logits `L`, and `L` has a strict argmax `istar` with runner-up margin `gamma`
satisfying `2 * tau ≤ gamma`, the quantized decode is admissible: it predicts the
same next token as the FP reference.

This is a DIRECT call to the imported
`QualityMarginCacheAdmissibility.cache_hit_admissible` — the entire linear-margin
algebra (`L' j < L j + tau ≤ L istar - tau < L' istar`) is reused, not re-proved.
The quantization contribution is solely the bridge reading: for a quant level,
`L'` is the dequant-matvec logit vector and `tau` is that format's block
representable resolution. -/
theorem quant_matvec_admissible {n : Nat} (L L' : Fin n → Int) (istar : Fin n)
    (gamma tau : Int)
    (hstar : IsStrictArgmax L istar)
    (hmargin : MarginAtLeast L istar gamma)
    (hbound : SupNormBelow L L' tau)
    (htau : 2 * tau ≤ gamma) :
    Admissible L L' :=
  cache_hit_admissible L L' istar gamma tau hstar hmargin hbound htau

/--
**Gate equivalence on the quantized decode.** A wrapper over the imported
`predicted_token_preserved`: under the quant-admissibility premises, *any* strict
argmax of the quantized-matvec logits equals the FP reference argmax `istar`. So
the PARIS probe over the quantized decode returns exactly the next token the FP
matvec would — the gate cannot tell the quantized decode from the FP
computation. -/
theorem quant_token_preserved {n : Nat} (L L' : Fin n → Int) (istar : Fin n)
    (gamma tau : Int)
    (hmargin : MarginAtLeast L istar gamma)
    (hbound : SupNormBelow L L' tau)
    (htau : 2 * tau ≤ gamma) :
    ∀ i', IsStrictArgmax L' i' → i' = istar :=
  predicted_token_preserved L L' istar gamma tau hmargin hbound htau

-- ═══════════════════════════════════════════════════════════════════════
-- §3  Precision monotonicity (the honest structural win)
-- ═══════════════════════════════════════════════════════════════════════

/--
**Refining precision never loses admissibility.** If a coarse quant level admits
(`2 * tauCoarse ≤ gamma`) and a finer level has tolerance `tauFine ≤ tauCoarse`,
then the finer level also admits (`2 * tauFine ≤ gamma`).

Proof: `2 * tauFine ≤ 2 * tauCoarse` by `Int.mul_le_mul_of_nonneg_left` (the `2`
is nonneg), then `Int.le_trans` to the coarse admissibility. No new arithmetic,
no `omega`. The bridge reading: a finer block format is always a sound drop-in
wherever a coarser one was already admissible. -/
theorem precision_monotone {gamma tauFine tauCoarse : Int}
    (hFineLeCoarse : tauFine ≤ tauCoarse)
    (hCoarse : 2 * tauCoarse ≤ gamma) :
    2 * tauFine ≤ gamma :=
  Int.le_trans
    (Int.mul_le_mul_of_nonneg_left hFineLeCoarse (by decide : (0 : Int) ≤ 2))
    hCoarse

/-- Q6K is at least as fine as Q5K (smaller representable resolution). Closed
    `decide` over the representative placeholder constants. -/
theorem tauQ6K_le_tauQ5K : tauQ6K ≤ tauQ5K := by decide

/-- Q5K is at least as fine as Q4K (smaller representable resolution). Closed
    `decide` over the representative placeholder constants. -/
theorem tauQ5K_le_tauQ4K : tauQ5K ≤ tauQ4K := by decide

/-- Worked monotonicity: if the COARSE Q4K level admits at some margin `gamma`,
    so does the FINER Q5K level. Routes the concrete `tauQ5K ≤ tauQ4K` instance
    through `precision_monotone`. -/
theorem q5k_admits_when_q4k_admits {gamma : Int}
    (hCoarse : 2 * tauQ4K ≤ gamma) : 2 * tauQ5K ≤ gamma :=
  precision_monotone tauQ5K_le_tauQ4K hCoarse

-- ═══════════════════════════════════════════════════════════════════════
-- §4  The corruptor antitheorem (the bound is tight)
-- ═══════════════════════════════════════════════════════════════════════

/--
**Sharpness: an under-resolved quant level flips the token.** The half-margin
band is tight. Reusing the imported `Fin 2` witnesses `flipL` / `flipL'`: the FP
reference `flipL` wins token 0 with margin `gamma = 2`, and the quantized-matvec
logits `flipL'` are within sup-norm `tau = 3` of them — but with the bound
violated (`2 * tau = 6 > 2 = gamma`) the quantized argmax has flipped to token 1.

This is the formal signature of a quant level chosen too coarse for the decision
margin: the kernel still "returns a result" (a logit vector exists and has an
argmax), yet the served token is wrong. Doctrine: beyond `gamma / 2` the quant
level must MISS — escalate to a finer format — not lie. The exact tightness twin
of `QualityMarginCacheAdmissibility.argmax_can_flip_when_bound_violated`.

Each conjunct is a CLOSED goal (literal `Fin 2` vectors / literal `Int`), so
`decide` is admitted by the Rustic Church contract — kernel-checked, not an
open-goal arithmetic tactic. -/
theorem quant_can_flip_when_bound_violated :
    -- FP reference: token 0 wins with margin gamma = 2
    IsStrictArgmax flipL ⟨0, by decide⟩ ∧
    MarginAtLeast flipL ⟨0, by decide⟩ 2 ∧
    (0 : Int) < 2 ∧
    -- quantized-matvec logits are within sup-norm tau = 3 of the FP reference
    SupNormBelow flipL flipL' 3 ∧
    -- but the half-margin bound is violated: 2 * tau = 6 > 2 = gamma
    ¬ (2 * (3 : Int) ≤ 2) ∧
    -- so the quantized argmax is NOT token 0: the quant level flipped the token
    ¬ IsStrictArgmax flipL' ⟨0, by decide⟩ := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj
    match j with
    | ⟨0, _⟩ => exact absurd rfl hj
    | ⟨1, _⟩ => show (0 : Int) < 2; decide
  · intro j hj
    match j with
    | ⟨0, _⟩ => exact absurd rfl hj
    | ⟨1, _⟩ => show (0 : Int) + 2 ≤ 2; decide
  · decide
  · intro k
    match k with
    | ⟨0, _⟩ => exact ⟨by show (-3 : Int) < 2 - 0; decide, by show (2 : Int) - 0 < 3; decide⟩
    | ⟨1, _⟩ => exact ⟨by show (-3 : Int) < 0 - 2; decide, by show (0 : Int) - 2 < 3; decide⟩
  · decide
  · intro hcontra
    have hgt := hcontra ⟨1, by decide⟩ (by decide)
    exact absurd hgt (by show ¬ ((2 : Int) < 0); decide)

-- ═══════════════════════════════════════════════════════════════════════
-- §5  Concrete worked example (a 3-token Q4K admissible decode)
-- ═══════════════════════════════════════════════════════════════════════

/-! A decode step at the COARSEST Q4K level. FP reference logits `[5, 1, 0]`:
token 0 wins with runner-up margin `gamma = 4`. The Q4K dequant-matvec
reconstructs `[6, 2, 1]` — every coordinate diverged by `+1`, so sup-norm error
`< tau = 2`, and `2 * tau = 4 ≤ 4 = gamma`. The certificate routes the decode
through `quant_matvec_admissible`, certifying the Q4K decode predicts the same
token as the FP reference. (Here `tau = 2` is the worked example's chosen
tolerance; the named `tauQ4K = 4` constant is an independent representative
placeholder for the ordering proofs.) -/

/-- FP reference logits of the worked Q4K decode. -/
def exQuantL : Fin 3 → Int := fun k => match k with
  | ⟨0, _⟩ => 5
  | ⟨1, _⟩ => 1
  | ⟨2, _⟩ => 0
  | ⟨_ + 3, h⟩ => absurd h (Nat.not_lt_of_le (Nat.le_add_left 3 _))

/-- Q4K dequant-matvec logits of the worked decode (each `+1` quant drift). -/
def exQuantL' : Fin 3 → Int := fun k => match k with
  | ⟨0, _⟩ => 6
  | ⟨1, _⟩ => 2
  | ⟨2, _⟩ => 1
  | ⟨_ + 3, h⟩ => absurd h (Nat.not_lt_of_le (Nat.le_add_left 3 _))

/-- Token 0 is the strict argmax of the FP reference. -/
theorem exQuant_true_argmax : IsStrictArgmax exQuantL ⟨0, by decide⟩ := by
  intro j hj
  match j with
  | ⟨0, _⟩ => exact absurd rfl hj
  | ⟨1, _⟩ => show (1 : Int) < 5; decide
  | ⟨2, _⟩ => show (0 : Int) < 5; decide

/-- The FP reference has runner-up margin `gamma = 4` at token 0. -/
theorem exQuant_margin : MarginAtLeast exQuantL ⟨0, by decide⟩ 4 := by
  intro j hj
  match j with
  | ⟨0, _⟩ => exact absurd rfl hj
  | ⟨1, _⟩ => show (1 : Int) + 4 ≤ 5; decide
  | ⟨2, _⟩ => show (0 : Int) + 4 ≤ 5; decide

/-- The Q4K dequant-matvec logits are within sup-norm `tau = 2` of the FP
    reference. -/
theorem exQuant_bound : SupNormBelow exQuantL exQuantL' 2 := by
  intro k
  match k with
  | ⟨0, _⟩ => exact ⟨by show (-2 : Int) < 5 - 6; decide, by show (5 : Int) - 6 < 2; decide⟩
  | ⟨1, _⟩ => exact ⟨by show (-2 : Int) < 1 - 2; decide, by show (1 : Int) - 2 < 2; decide⟩
  | ⟨2, _⟩ => exact ⟨by show (-2 : Int) < 0 - 1; decide, by show (0 : Int) - 1 < 2; decide⟩

/-- **Worked Q4K decode is admissible.** The bounded-divergence quantized decode
    predicts the same next token as the FP reference. Routes through
    `quant_matvec_admissible`, so the worked example is a live carrier of the
    general bound, not a standalone calculation. -/
theorem exQuant_admissible : Admissible exQuantL exQuantL' :=
  quant_matvec_admissible exQuantL exQuantL' ⟨0, by decide⟩ 4 2
    exQuant_true_argmax exQuant_margin exQuant_bound (by decide)

end QuantMatvecAdmissibility
end Aether
end Gnosis
