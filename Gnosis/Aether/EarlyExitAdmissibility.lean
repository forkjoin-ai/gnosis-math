import Init
import Gnosis.QualityMarginCacheAdmissibility

/-!
# Provable early-exit (layer-skip) admissibility (Rustic Church, Init-only)

The biggest fastpath in distributed inference: if the layer-`k` partial logit
projection has *already decided* the argmax, skip layers `k+1 .. N`. This module
certifies that early exit is **lossless** — it can never change the emitted token
— under exactly the same half-margin bound `2 * tau ≤ gamma` the quality-margin
cache certificate uses. CALM-style early exit, but PROVEN.

## The decomposition (what the τ means here)

Write the final logits as the layer-`k` partial projection plus a perturbation:

```text
  L  =  L_k  +  (L − L_k),       ‖L − L_k‖∞  ≤  tauRemaining
```

where `L_k = lmHead(rmsNorm(resid_k))` is the cheap projection of the layer-`k`
residual, and the remaining layers `k+1 .. N` can only move each logit by at most
`tauRemaining`. The bound is a **Lipschitz product**:

```text
  tauRemaining  =  (∏ over remaining layers ℓ of L_ℓ) · ‖resid_k‖
```

— each remaining layer contributes a per-layer Lipschitz gain `L_ℓ` (a sound
over-estimate computed from its weight norms; see the runtime module), folded
multiplicatively over the remaining layers, times the current residual norm.

## The early-exit rule (one line, a DIRECT reuse of the cache bound)

If the partial projection `L_k` has a strict argmax `istar` with runner-up margin
`gamma`, and the *true* final logits `L` differ from `L_k` by at most
`tauRemaining` in sup-norm with `2 * tauRemaining ≤ gamma`, then `L` ALSO has
strict argmax `istar`: the token is already decided at layer `k`, so skipping the
remaining layers emits the identical token. This is literally
`QualityMarginCacheAdmissibility.cache_hit_admissible` with the layer-`k`
projection `L_k` as the "approximation" `L'` and the final logits `L` as the
"truth" `L` — the linear-margin algebra is reused wholesale, not re-proved.

## Soundness direction (never exit too eagerly)

`tauRemaining` is a PRODUCT over the remaining layers. More remaining layers ⇒
larger product (each factor ≥ 1 gain) ⇒ larger `tauRemaining` ⇒ `2*tau ≤ gamma`
is HARDER to satisfy ⇒ harder to exit. So the bound is conservative in the safe
direction: an over-estimate of the remaining perturbation can only make the gate
DECLINE to exit (a spurious continue), never trigger a too-early exit that would
flip the token. The antitheorem `exit_can_flip_when_too_early` proves the
boundary is tight: exiting when `2*tauRemaining > gamma` can serve the wrong
token.

Init-only per `RUSTIC_CHURCH.md`: `import Init` + the sibling gnosis module only;
no Mathlib, no `omega`, no `simp`/`decide` on open-variable goals. `decide`
appears only on CLOSED goals (literal `Fin n` vectors / literal `Int`/`Nat`).
`#print axioms` is `propext` only.
-/

open Gnosis.QualityMarginCacheAdmissibility

namespace Gnosis
namespace Aether
namespace EarlyExitAdmissibility

-- ═══════════════════════════════════════════════════════════════════════
-- §1  The early-exit safety theorem (thin reuse of the cache bound)
-- ═══════════════════════════════════════════════════════════════════════

/--
**`early_exit_safe` — the layer-`k` token is the final token.** Given the
layer-`k` partial projection `Lk` has a strict argmax `istar` with runner-up
margin `gamma`, the final logits `L` are within sup-norm `tauRemaining` of `Lk`
(`SupNormBelow Lk L tauRemaining` — the remaining layers' total perturbation),
and `2 * tauRemaining ≤ gamma`, then `istar` is the strict argmax of the FINAL
logits `L` as well. Hence skipping layers `k+1 .. N` and emitting `istar` is
lossless: it equals the token the full stack would emit.

This is a DIRECT instantiation of
`QualityMarginCacheAdmissibility.argmax_preserved`: the layer-`k` projection `Lk`
plays the role of the "true" reference whose margin we measure, and the final
logits `L` play the role of the "substituted" vector within `tauRemaining`. The
roles are symmetric in the bound (`SupNormBelow` is two-sided), so the margin
measured at `Lk` certifies the argmax of `L`. No `omega`; the linear-margin
algebra is reused, not re-proved. -/
theorem early_exit_safe {n : Nat} (Lk L : Fin n → Int) (istar : Fin n)
    (gamma tauRemaining : Int)
    (hmargin : MarginAtLeast Lk istar gamma)
    (hbound : SupNormBelow Lk L tauRemaining)
    (htau : 2 * tauRemaining ≤ gamma) :
    IsStrictArgmax L istar :=
  argmax_preserved Lk L istar gamma tauRemaining hmargin hbound htau

/--
**`early_exit_admissible` — the exit serves the same token (admissibility view).**
Packaging `early_exit_safe` as an `Admissible` pair: under the same premises plus
a strict argmax of `Lk`, the partial projection `Lk` and the final logits `L`
share the strict argmax `istar`. So the early exit is gate-equivalent to running
the full stack — the served token is identical.

Routes through `QualityMarginCacheAdmissibility.cache_hit_admissible`. -/
theorem early_exit_admissible {n : Nat} (Lk L : Fin n → Int) (istar : Fin n)
    (gamma tauRemaining : Int)
    (hstar : IsStrictArgmax Lk istar)
    (hmargin : MarginAtLeast Lk istar gamma)
    (hbound : SupNormBelow Lk L tauRemaining)
    (htau : 2 * tauRemaining ≤ gamma) :
    Admissible Lk L :=
  cache_hit_admissible Lk L istar gamma tauRemaining hstar hmargin hbound htau

/--
**Gate equivalence at the exit.** Under the early-exit premises, *any* strict
argmax of the final logits `L` equals the layer-`k` argmax `istar`. So the token
decided at layer `k` is provably the full-stack token: the early-exit decode and
the full-depth decode emit the identical token. -/
theorem early_exit_token_preserved {n : Nat} (Lk L : Fin n → Int) (istar : Fin n)
    (gamma tauRemaining : Int)
    (hmargin : MarginAtLeast Lk istar gamma)
    (hbound : SupNormBelow Lk L tauRemaining)
    (htau : 2 * tauRemaining ≤ gamma) :
    ∀ i', IsStrictArgmax L i' → i' = istar :=
  predicted_token_preserved Lk L istar gamma tauRemaining hmargin hbound htau

-- ═══════════════════════════════════════════════════════════════════════
-- §2  The per-layer Lipschitz-product accumulator (the τ_remaining shape)
-- ═══════════════════════════════════════════════════════════════════════

/--
The remaining-layers Lipschitz product, folded structurally over a list of
per-layer Nat gain bounds. `lipProduct [L_{k+1}, ..., L_N]` = `∏ L_ℓ`. Each
factor is a sound per-layer gain over-estimate (computed from layer weight norms
at runtime). The fold is `Nat` and structural (no `omega`). -/
def lipProduct : List Nat → Nat
  | [] => 1
  | g :: rest => g * lipProduct rest

/--
`tauRemaining = lipProduct(remaining gains) · residNorm`, the Int-scaled sup-norm
bound on `‖L − L_k‖∞`. `residNorm` is the Int-scaled `‖resid_k‖`; the gain list is
the remaining per-layer Lipschitz bounds. The cast to `Int` is faithful (the
product and norm are magnitudes; argmax is scale-invariant). -/
def tauRemaining (gains : List Nat) (residNorm : Nat) : Int :=
  ((lipProduct gains * residNorm : Nat) : Int)

/-- The empty product is `1`. -/
theorem lipProduct_nil : lipProduct [] = 1 := rfl

/-- Prepending a layer multiplies the product by that layer's gain. -/
theorem lipProduct_cons (g : Nat) (rest : List Nat) :
    lipProduct (g :: rest) = g * lipProduct rest := rfl

/--
**`lipProduct_pos` — the product is positive when every gain is positive.** A
per-layer Lipschitz gain is always at least `1` (a layer cannot shrink the
sup-norm below identity in this conservative model), so the product is positive.
Structural induction on the list; each step is `Nat.mul_pos`. No `omega`. -/
theorem lipProduct_pos : ∀ (gains : List Nat),
    (∀ g, g ∈ gains → 0 < g) → 0 < lipProduct gains
  | [], _ => by decide
  | g :: rest, hpos => by
      have hg : 0 < g := hpos g (List.Mem.head rest)
      have hrest : 0 < lipProduct rest :=
        lipProduct_pos rest (fun x hx => hpos x (List.Mem.tail g hx))
      rw [lipProduct_cons]
      exact Nat.mul_pos hg hrest

/--
**`lipProduct_monotone_cons` — more remaining layers ⇒ a larger product.** Adding
one more remaining layer (gain `g ≥ 1`) never shrinks the Lipschitz product:
`lipProduct rest ≤ lipProduct (g :: rest)`. This is the structural heart of the
soundness direction — a longer remaining tail can only INFLATE `tauRemaining`.

Proof: `lipProduct rest = 1 * lipProduct rest ≤ g * lipProduct rest`
(`Nat.mul_le_mul_right` with `1 ≤ g`). No `omega`. -/
theorem lipProduct_monotone_cons (g : Nat) (rest : List Nat) (hg : 1 ≤ g) :
    lipProduct rest ≤ lipProduct (g :: rest) := by
  rw [lipProduct_cons]
  have h1 : 1 * lipProduct rest ≤ g * lipProduct rest :=
    Nat.mul_le_mul_right (lipProduct rest) hg
  rw [Nat.one_mul] at h1
  exact h1

/--
**`tauRemaining_monotone_cons` — more remaining layers ⇒ a larger `tauRemaining`
⇒ harder to exit.** Prepending one more remaining layer (gain `g ≥ 1`) never
shrinks `tauRemaining`. Since the early-exit gate fires only when
`2 * tauRemaining ≤ gamma`, a larger `tauRemaining` makes the gate HARDER to
satisfy: the bound is conservative in the safe direction (an over-estimate of the
remaining perturbation can only DECLINE an exit, never trigger a too-early one).

Lifts `lipProduct_monotone_cons` through `· * residNorm` (`Nat.mul_le_mul_right`)
and the `Nat → Int` cast (`Int.ofNat_le.mpr`). No `omega`. -/
theorem tauRemaining_monotone_cons (g : Nat) (rest : List Nat) (residNorm : Nat)
    (hg : 1 ≤ g) :
    tauRemaining rest residNorm ≤ tauRemaining (g :: rest) residNorm := by
  unfold tauRemaining
  apply Int.ofNat_le.mpr
  exact Nat.mul_le_mul_right residNorm (lipProduct_monotone_cons g rest hg)

/--
**`exit_harder_with_more_layers` — the soundness corollary, stated at the gate.**
If the early-exit gate ADMITS at layer `k` with the longer remaining tail
`g :: rest` (i.e. `2 * tauRemaining (g :: rest) residNorm ≤ gamma`), then it would
also admit with the shorter tail `rest`. Contrapositive reading: you can only ever
exit "more eagerly" with FEWER remaining layers — never the reverse. So an
over-counted remaining tail is always safe (it only suppresses exits).

Proof: `2 * tauRemaining rest ≤ 2 * tauRemaining (g::rest) ≤ gamma` via
`Int.mul_le_mul_of_nonneg_left` on the monotonicity lemma, then `Int.le_trans`.
No `omega`. -/
theorem exit_harder_with_more_layers (g : Nat) (rest : List Nat) (residNorm : Nat)
    (gamma : Int) (hg : 1 ≤ g)
    (hadmitLong : 2 * tauRemaining (g :: rest) residNorm ≤ gamma) :
    2 * tauRemaining rest residNorm ≤ gamma :=
  Int.le_trans
    (Int.mul_le_mul_of_nonneg_left
      (tauRemaining_monotone_cons g rest residNorm hg)
      (by decide : (0 : Int) ≤ 2))
    hadmitLong

-- ═══════════════════════════════════════════════════════════════════════
-- §3  The antitheorem (Sardis signature: exiting too early flips the token)
-- ═══════════════════════════════════════════════════════════════════════

/--
**Sharpness: exiting too early flips the token.** The half-margin band is tight
for early exit too. Reusing the imported `Fin 2` flip witnesses: the layer-`k`
projection `flipL` decides token 0 with margin `gamma = 2`, and the FINAL logits
`flipL'` are within sup-norm `tauRemaining = 3` of it — but with the bound
violated (`2 * tauRemaining = 6 > 2 = gamma`) the FINAL argmax has flipped to
token 1. So an early exit taken at layer `k` here would emit token 0 while the
full stack emits token 1: a WRONG token.

This is the formal signature of exiting before the token is decided: the gate
"reports a confident exit" over a logit gap the remaining layers were still large
enough to overturn. Doctrine: when `2 * tauRemaining > gamma`, do NOT exit —
continue the remaining layers. The exact tightness twin of
`QualityMarginCacheAdmissibility.argmax_can_flip_when_bound_violated`, read for
layer-skip instead of caching.

Each conjunct is a CLOSED goal (literal `Fin 2` vectors / literal `Int`), so
`decide` is admitted by the Rustic Church contract — kernel-checked, not an
open-goal arithmetic tactic. -/
theorem exit_can_flip_when_too_early :
    -- layer-k projection decides token 0 with margin gamma = 2
    IsStrictArgmax flipL ⟨0, by decide⟩ ∧
    MarginAtLeast flipL ⟨0, by decide⟩ 2 ∧
    (0 : Int) < 2 ∧
    -- final logits are within sup-norm tauRemaining = 3 of the layer-k projection
    SupNormBelow flipL flipL' 3 ∧
    -- but the half-margin bound is violated: 2 * tauRemaining = 6 > 2 = gamma
    ¬ (2 * (3 : Int) ≤ 2) ∧
    -- so the FINAL argmax is NOT token 0: the early exit would emit a wrong token
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
-- §4  Concrete worked example (a 3-token early exit routed through the bound)
-- ═══════════════════════════════════════════════════════════════════════

/-! A decode step where the token is ALREADY decided at layer `k`. The layer-`k`
partial projection `[5, 1, 0]` decides token 0 with runner-up margin `gamma = 4`.
The remaining layers perturb each logit by `+1` (so the final logits are
`[6, 2, 1]`), giving sup-norm `tauRemaining = 2` with `2 * tauRemaining = 4 ≤ 4 =
gamma`. The early-exit certificate routes through `early_exit_admissible`,
certifying that exiting at layer `k` emits the same token (0) the full stack would.

The `tauRemaining = 2` here is realized by a remaining Lipschitz product `2` and a
residual norm `1` (`lipProduct [2] = 2`, `tauRemaining [2] 1 = 2`) — see
`ex_tau_realized` — so the worked tolerance is a live instance of the §2
accumulator, not a free literal. -/

/-- Layer-`k` partial projection logits of the worked example. -/
def exLk : Fin 3 → Int := fun k => match k with
  | ⟨0, _⟩ => 5
  | ⟨1, _⟩ => 1
  | ⟨2, _⟩ => 0
  | ⟨_ + 3, h⟩ => absurd h (Nat.not_lt_of_le (Nat.le_add_left 3 _))

/-- Final (full-stack) logits of the worked example (each `+1` from remaining layers). -/
def exLfinal : Fin 3 → Int := fun k => match k with
  | ⟨0, _⟩ => 6
  | ⟨1, _⟩ => 2
  | ⟨2, _⟩ => 1
  | ⟨_ + 3, h⟩ => absurd h (Nat.not_lt_of_le (Nat.le_add_left 3 _))

/-- Token 0 is the strict argmax of the layer-`k` projection. -/
theorem exLk_argmax : IsStrictArgmax exLk ⟨0, by decide⟩ := by
  intro j hj
  match j with
  | ⟨0, _⟩ => exact absurd rfl hj
  | ⟨1, _⟩ => show (1 : Int) < 5; decide
  | ⟨2, _⟩ => show (0 : Int) < 5; decide

/-- The layer-`k` projection has runner-up margin `gamma = 4` at token 0. -/
theorem exLk_margin : MarginAtLeast exLk ⟨0, by decide⟩ 4 := by
  intro j hj
  match j with
  | ⟨0, _⟩ => exact absurd rfl hj
  | ⟨1, _⟩ => show (1 : Int) + 4 ≤ 5; decide
  | ⟨2, _⟩ => show (0 : Int) + 4 ≤ 5; decide

/-- The final logits are within sup-norm `tauRemaining = 2` of the layer-`k`
    projection. -/
theorem exLk_bound : SupNormBelow exLk exLfinal 2 := by
  intro k
  match k with
  | ⟨0, _⟩ => exact ⟨by show (-2 : Int) < 5 - 6; decide, by show (5 : Int) - 6 < 2; decide⟩
  | ⟨1, _⟩ => exact ⟨by show (-2 : Int) < 1 - 2; decide, by show (1 : Int) - 2 < 2; decide⟩
  | ⟨2, _⟩ => exact ⟨by show (-2 : Int) < 0 - 1; decide, by show (0 : Int) - 1 < 2; decide⟩

/-- The worked `tauRemaining = 2` is a live instance of the §2 accumulator:
    a single remaining layer with gain `2` over a residual of norm `1`. -/
theorem ex_tau_realized : tauRemaining [2] 1 = 2 := by decide

/-- **The worked early exit is admissible.** The token decided at layer `k` (0)
    equals the full-stack token. Routes through `early_exit_admissible`, so the
    worked example is a live carrier of the general bound, not a standalone
    calculation. -/
theorem ex_early_exit_admissible : Admissible exLk exLfinal :=
  early_exit_admissible exLk exLfinal ⟨0, by decide⟩ 4 2
    exLk_argmax exLk_margin exLk_bound (by decide)

/-- **The worked exit emits the full-stack token.** `early_exit_safe` directly:
    the final logits also have strict argmax token 0. -/
theorem ex_final_argmax : IsStrictArgmax exLfinal ⟨0, by decide⟩ :=
  early_exit_safe exLk exLfinal ⟨0, by decide⟩ 4 2
    exLk_margin exLk_bound (by decide)

end EarlyExitAdmissibility
end Aether
end Gnosis
