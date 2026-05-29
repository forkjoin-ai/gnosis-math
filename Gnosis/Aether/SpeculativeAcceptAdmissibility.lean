import Init
import Gnosis.QualityMarginCacheAdmissibility

/-!
# Speculative-decode accept admissibility (Rustic Church, Init-only)

Speculative decoding drafts tokens cheaply (a small model / Q4K / ternary
kernel) and verifies them against the real model. The naive accept rule is
*probabilistic* — accept the draft if a random-coin test passes — and can serve
a token the greedy verifier would NOT have emitted. This module proves a
*deterministic, token-identical* accept rule instead:

> Accept the draft's predicted token `istar` iff the VERIFIER'S runner-up margin
> `gamma_verify` satisfies `2 * tau_draft <= gamma_verify`, where `tau_draft`
> is a sup-norm bound on `‖L_draft − L_verify‖∞` (how far the draft logits sit
> from the verify logits). When that holds, the draft's argmax EQUALS the
> verifier's greedy argmax PROVABLY — the accepted token is exactly what greedy
> verification would emit. Beyond the bound: reject (fall back to verify), never
> accept a wrong token.

This is the SAME half-margin bound as `QualityMarginCacheAdmissibility` (the
cache-hit / quant rule), applied to the draft/verify pair: the verifier plays
the role of the true logits `L`, the draft plays the substituted logits `L'`,
and `tau_draft` is the substitution tolerance. So the whole linear-margin
algebra (`L' j < L j + tau ≤ L istar - tau < L' istar`) is REUSED wholesale —
this module re-instantiates the imported core, it does NOT re-prove it.

## The bridge rule (what stays OUTSIDE the theorem)

The draft model's float numerics — its weights, its quant format, the actual
draft logits — stay OUTSIDE the theorem. They enter only through one Int-scaled
quantity: `tauDraft`, a TRUE sup-norm upper bound on `‖L_draft − L_verify‖∞`.
This is the same quantize-then-decide bridge the sibling modules use: the argmax
decision is scale-invariant, so the bound is written scale-free as
`2 * tauDraft ≤ gamma`. The honest caller computes `tauDraft` soundly (e.g. via
the Hölder half-step bound in `margin-gate.ts`'s `tauForLevel`, or a calibrated
draft-vs-verify divergence) and SUPPLIES IT AS A PARAMETER. A theorem cannot
manufacture `tauDraft`; if the caller cannot bound the draft's divergence
soundly, it must REJECT (fall back to verify), never fake an accept.

## The two halves, both load-bearing

- **`accept_is_exact` (the bound / live witness).** Under
  `MarginAtLeast L_verify istar gamma`, `SupNormBelow L_verify L_draft tauDraft`,
  and `2 * tauDraft ≤ gamma`, BOTH the draft and the verifier have `istar` as
  their strict argmax. The accepted token is token-identical to greedy
  verification. Direct call to `cache_hit_admissible` (with `L = verify`,
  `L' = draft`).
- **`accept_can_be_wrong_when_margin_too_small` (the antitheorem / Sardis
  signature).** The bound is tight: a draft within `tauDraft` of the verifier
  but with `2 * tauDraft > gamma` can have a DIFFERENT argmax — accepting it
  would serve the wrong token. So beyond `gamma / 2` the gate must REJECT, not
  lie. (Reuses the imported `Fin 2` flip witnesses `flipL` / `flipL'`.)

Init-only per `RUSTIC_CHURCH.md`: `import Init` + the sibling gnosis module only;
no Mathlib, no `omega`, no `simp`/`decide` on open-variable goals. `decide`
appears only on CLOSED goals (literal `Fin n` vectors / literal `Int`
tolerances).
-/

open Gnosis.QualityMarginCacheAdmissibility

namespace Gnosis
namespace Aether
namespace SpeculativeAcceptAdmissibility

-- ═══════════════════════════════════════════════════════════════════════
-- §1  The accept rule (thin reuse of the imported core)
-- ═══════════════════════════════════════════════════════════════════════

/--
**Speculative accept is exact (the τ rule).** If the VERIFIER's logits
`L_verify` have a strict argmax `istar` with runner-up margin `gamma`, and the
draft logits `L_draft` are within sup-norm `tauDraft` of the verifier with
`2 * tauDraft ≤ gamma`, then BOTH the draft and the verifier have `istar` as
their strict argmax. The accepted draft token is token-identical to what greedy
verification would emit.

This is a DIRECT call to the imported
`QualityMarginCacheAdmissibility.cache_hit_admissible` (with `L = verify`,
`L' = draft`). The entire linear-margin algebra is reused, not re-proved. The
speculative-decode contribution is solely the bridge reading: `L'` is the
draft-model logit vector and `tau` is a sound bound on the draft↔verify
divergence.

We return the pair `IsStrictArgmax L_verify istar ∧ IsStrictArgmax L_draft istar`
directly (rather than `Admissible`, which existentially hides `istar`) so the
caller can read off that the SHARED winner is the verifier's named `istar`. -/
theorem accept_is_exact {n : Nat} (L_verify L_draft : Fin n → Int) (istar : Fin n)
    (gamma tauDraft : Int)
    (hstar : IsStrictArgmax L_verify istar)
    (hmargin : MarginAtLeast L_verify istar gamma)
    (hbound : SupNormBelow L_verify L_draft tauDraft)
    (htau : 2 * tauDraft ≤ gamma) :
    IsStrictArgmax L_draft istar ∧ IsStrictArgmax L_verify istar :=
  ⟨argmax_preserved L_verify L_draft istar gamma tauDraft hmargin hbound htau, hstar⟩

/--
**The accepted token equals the verifier's token.** A wrapper over the imported
`predicted_token_preserved`: under the accept premises, *any* strict argmax of
the draft logits equals the verifier's argmax `istar`. So the accepted token —
the draft's predicted token — is exactly the token greedy verification emits.
The gate cannot accept a token the verifier would not have produced. -/
theorem accepted_token_equals_verify {n : Nat} (L_verify L_draft : Fin n → Int)
    (istar : Fin n) (gamma tauDraft : Int)
    (hmargin : MarginAtLeast L_verify istar gamma)
    (hbound : SupNormBelow L_verify L_draft tauDraft)
    (htau : 2 * tauDraft ≤ gamma) :
    ∀ iDraft, IsStrictArgmax L_draft iDraft → iDraft = istar :=
  predicted_token_preserved L_verify L_draft istar gamma tauDraft hmargin hbound htau

-- ═══════════════════════════════════════════════════════════════════════
-- §2  The antitheorem (Sardis signature: the bound is tight)
-- ═══════════════════════════════════════════════════════════════════════

/--
**Sharpness: accepting beyond half the margin serves the wrong token.** The
half-margin band is tight. Reusing the imported `Fin 2` witnesses `flipL` /
`flipL'`: the VERIFIER `flipL` wins token 0 with margin `gamma = 2`, and the
draft logits `flipL'` are within sup-norm `tauDraft = 3` of the verifier — but
with the bound violated (`2 * tauDraft = 6 > 2 = gamma`) the draft's argmax has
flipped to token 1. So a gate that ACCEPTED token 0 here on the strength of the
draft would serve a token the verifier would NOT emit.

Doctrine: beyond `gamma / 2` the gate must REJECT (fall back to greedy verify),
not lie. This is the exact tightness twin of
`QualityMarginCacheAdmissibility.argmax_can_flip_when_bound_violated` and
`QuantMatvecAdmissibility.quant_can_flip_when_bound_violated`.

Each conjunct is a CLOSED goal (literal `Fin 2` vectors / literal `Int`), so
`decide` is admitted by the Rustic Church contract — kernel-checked, not an
open-goal arithmetic tactic. -/
theorem accept_can_be_wrong_when_margin_too_small :
    -- Verifier: token 0 wins with runner-up margin gamma = 2
    IsStrictArgmax flipL ⟨0, by decide⟩ ∧
    MarginAtLeast flipL ⟨0, by decide⟩ 2 ∧
    (0 : Int) < 2 ∧
    -- draft logits are within sup-norm tauDraft = 3 of the verifier
    SupNormBelow flipL flipL' 3 ∧
    -- but the half-margin accept bound is violated: 2 * tauDraft = 6 > 2 = gamma
    ¬ (2 * (3 : Int) ≤ 2) ∧
    -- so the draft's argmax is NOT the verifier's token 0: accepting it would lie
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
-- §3  Concrete worked example (a 3-token accepted draft)
-- ═══════════════════════════════════════════════════════════════════════

/-! A speculative-decode step. VERIFIER logits `[5, 1, 0]`: token 0 wins with
runner-up margin `gamma = 4`. The cheap draft model reconstructs `[6, 2, 1]` —
every coordinate diverged by `+1`, so sup-norm error `< tauDraft = 2`, and
`2 * tauDraft = 4 ≤ 4 = gamma`. The certificate routes the step through
`accept_is_exact`, certifying the accepted draft token equals the verifier's
greedy argmax (token 0). -/

/-- Verifier logits of the worked accepted-draft step. -/
def exVerify : Fin 3 → Int := fun k => match k with
  | ⟨0, _⟩ => 5
  | ⟨1, _⟩ => 1
  | ⟨2, _⟩ => 0
  | ⟨_ + 3, h⟩ => absurd h (Nat.not_lt_of_le (Nat.le_add_left 3 _))

/-- Draft logits of the worked accepted-draft step (each `+1` draft drift). -/
def exDraft : Fin 3 → Int := fun k => match k with
  | ⟨0, _⟩ => 6
  | ⟨1, _⟩ => 2
  | ⟨2, _⟩ => 1
  | ⟨_ + 3, h⟩ => absurd h (Nat.not_lt_of_le (Nat.le_add_left 3 _))

/-- Token 0 is the strict argmax of the verifier. -/
theorem exVerify_argmax : IsStrictArgmax exVerify ⟨0, by decide⟩ := by
  intro j hj
  match j with
  | ⟨0, _⟩ => exact absurd rfl hj
  | ⟨1, _⟩ => show (1 : Int) < 5; decide
  | ⟨2, _⟩ => show (0 : Int) < 5; decide

/-- The verifier has runner-up margin `gamma = 4` at token 0. -/
theorem exVerify_margin : MarginAtLeast exVerify ⟨0, by decide⟩ 4 := by
  intro j hj
  match j with
  | ⟨0, _⟩ => exact absurd rfl hj
  | ⟨1, _⟩ => show (1 : Int) + 4 ≤ 5; decide
  | ⟨2, _⟩ => show (0 : Int) + 4 ≤ 5; decide

/-- The draft logits are within sup-norm `tauDraft = 2` of the verifier. -/
theorem exDraft_bound : SupNormBelow exVerify exDraft 2 := by
  intro k
  match k with
  | ⟨0, _⟩ => exact ⟨by show (-2 : Int) < 5 - 6; decide, by show (5 : Int) - 6 < 2; decide⟩
  | ⟨1, _⟩ => exact ⟨by show (-2 : Int) < 1 - 2; decide, by show (1 : Int) - 2 < 2; decide⟩
  | ⟨2, _⟩ => exact ⟨by show (-2 : Int) < 0 - 1; decide, by show (0 : Int) - 1 < 2; decide⟩

/-- **Worked accept is exact.** The cheap draft token equals the verifier's
    greedy argmax (token 0). Routes through `accept_is_exact`, so the worked
    example is a live carrier of the general bound, not a standalone
    calculation. The left conjunct is the draft's strict argmax; the right is the
    verifier's — both are token 0. -/
theorem exAccept_is_exact :
    IsStrictArgmax exDraft ⟨0, by decide⟩ ∧ IsStrictArgmax exVerify ⟨0, by decide⟩ :=
  accept_is_exact exVerify exDraft ⟨0, by decide⟩ 4 2
    exVerify_argmax exVerify_margin exDraft_bound (by decide)

/-- **Worked accepted token equals the verifier's token.** Any strict argmax of
    the draft is token 0 — the verifier's greedy token. Routes through
    `accepted_token_equals_verify`. -/
theorem exAccept_token_equals_verify :
    ∀ iDraft, IsStrictArgmax exDraft iDraft → iDraft = ⟨0, by decide⟩ :=
  accepted_token_equals_verify exVerify exDraft ⟨0, by decide⟩ 4 2
    exVerify_margin exDraft_bound (by decide)

end SpeculativeAcceptAdmissibility
end Aether
end Gnosis
