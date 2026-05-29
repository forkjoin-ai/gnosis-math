import Init
import Gnosis.QualityMarginCacheAdmissibility

/-!
# Ternary-weight matvec is EXACT integer arithmetic (Rustic Church, Init-only)

The quantized-matvec certificates (`QuantMatvecAdmissibility`,
`QualityMarginCacheAdmissibility`) admit a float kernel only up to a sup-norm
tolerance `tau`: a Q4K/Q5K/Q6K dequantize-then-multiply lands *near* the FP
reference, and the gate survives only while `2 * tau ≤ gamma`. There is one
matvec where that whole apparatus collapses to nothing: a **ternary-weight**
matvec, weights drawn from `{-1, 0, +1}`.

When every weight is `-1`, `0`, or `+1`, the kernel `dot w x = Σ w k * x k` is
**pure integer arithmetic** — there is no float anywhere, no rounding, no block
codebook, no representable-resolution drift. So unlike a quantized float kernel,
the ENTIRE kernel is exactly provable: `tau = 0`, and the kernel output equals
its specification with **zero error term**. This is the "church-certified ground
truth" inference path — the corner of the quant certificate where the bound is
not merely *satisfiable* but vacuous.

Model: input `x : Fin m → Int`, a ternary weight row `w : Fin m → Int` with each
`w k ∈ {-1, 0, +1}`, output the dot product `dot m w x = Σ_{k < m} w k * x k`,
computed by structural recursion over the `Nat` bound (Init-only, no Mathlib).

Init-only discipline per `RUSTIC_CHURCH.md`: `import Init` + the sibling gnosis
module only (for `IsStrictArgmax`); **no `omega`**, no Mathlib, no `simp`/`decide`
on open-variable goals. `decide` appears only on CLOSED goals (literal `Fin n`
vectors / literal `Int`). The per-weight exactness facts close on the `Int`
cookbook (`Int.zero_mul`, `Int.one_mul`, `Int.neg_one_mul`); the fold induction
is structural on the `Nat` bound (the `+1` clinamen).
-/

open Gnosis.QualityMarginCacheAdmissibility (IsStrictArgmax)

namespace Gnosis
namespace Aether
namespace TernaryMatvecExact

-- ═══════════════════════════════════════════════════════════════════════
-- §1  Ternary weights and the exact integer dot product
-- ═══════════════════════════════════════════════════════════════════════

/-- A weight row is **ternary** when every entry is `-1`, `0`, or `+1`. This is
the BitNet / `{-1,0,+1}` regime: the *only* representable weights, so there is no
codebook and no dequant float — the matvec is exact integer arithmetic. -/
def IsTernary {m : Nat} (w : Fin m → Int) : Prop :=
  ∀ k, w k = -1 ∨ w k = 0 ∨ w k = 1

/-- Exact integer dot product `Σ_{k < b} w ⟨k⟩ * x ⟨k⟩`, by structural recursion
on the `Nat` bound `b` (the `+1` clinamen). Init-only: no `Finset`, no `Fin.sum`,
no Mathlib. `b` is the prefix length; `m` is the full dimension that bounds the
indices. -/
def dotUpto {m : Nat} (w x : Fin m → Int) : (b : Nat) → b ≤ m → Int
  | 0,     _ => 0
  | b + 1, h =>
      let k : Fin m := ⟨b, Nat.lt_of_lt_of_le (Nat.lt_succ_self b) h⟩
      w k * x k + dotUpto w x b (Nat.le_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self b) h))

/-- The full ternary matvec row output: the exact dot product over all `m`
coordinates. No float, no error term — this is the kernel's literal output. -/
def dot {m : Nat} (w x : Fin m → Int) : Int :=
  dotUpto w x m (Nat.le_refl m)

-- ═══════════════════════════════════════════════════════════════════════
-- §2  Per-weight exactness facts (the {-1, 0, +1} contributions, EXACT)
-- ═══════════════════════════════════════════════════════════════════════

/-- A `0`-weight term contributes **exactly** nothing: `0 * x = 0`. This is the
pruning fact — a zero ternary weight drops the input with no residue. Closes by
`Int.zero_mul`; no `omega`, no error term. -/
theorem contribution_zero (xk : Int) : (0 : Int) * xk = 0 :=
  Int.zero_mul xk

/-- A `+1`-weight term contributes **exactly** the input: `1 * x = x`. Closes by
`Int.one_mul`. -/
theorem contribution_pos (xk : Int) : (1 : Int) * xk = xk :=
  Int.one_mul xk

/-- A `-1`-weight term contributes **exactly** the negated input: `(-1) * x = -x`.
Closes by `Int.neg_one_mul`. The signed-sum structure of a ternary dot is thus
exact: each term is `x k`, `0`, or `-x k`, never an approximation. -/
theorem contribution_neg (xk : Int) : (-1 : Int) * xk = -xk :=
  Int.neg_one_mul xk

/--
**`ternary_dot_exact` — the per-weight kernel-vs-spec exactness, bundled.** For a
ternary weight `wk ∈ {-1,0,+1}`, the term `wk * xk` is EXACTLY one of the three
signed contributions — `-xk`, `0`, or `xk` — with no error term. This is the
structural reason the whole `dot` is exact: it is a signed sum of the inputs, and
each summand is pinned to the input (or its negation, or zero) by an Init `Int`
identity. A quantized float kernel can only bound `|wk*xk - spec|`; here the gap
is identically `0`. -/
theorem ternary_dot_exact {wk xk : Int}
    (hw : wk = -1 ∨ wk = 0 ∨ wk = 1) :
    wk * xk = -xk ∨ wk * xk = 0 ∨ wk * xk = xk := by
  match hw with
  | Or.inl hneg => exact Or.inl (by rw [hneg]; exact Int.neg_one_mul xk)
  | Or.inr (Or.inl hzero) => exact Or.inr (Or.inl (by rw [hzero]; exact Int.zero_mul xk))
  | Or.inr (Or.inr hpos) => exact Or.inr (Or.inr (by rw [hpos]; exact Int.one_mul xk))

-- ═══════════════════════════════════════════════════════════════════════
-- §3  Per-term magnitude bound (each contribution sits in [-|xk|, |xk|])
-- ═══════════════════════════════════════════════════════════════════════

/--
**`ternary_contribution_bounded` — each term is sandwiched by `± xk` (for
non-negative `xk`).** Given `0 ≤ xk` and a ternary weight `wk`, the contribution
`wk * xk` lies in `[-xk, xk]`: `-xk ≤ wk * xk ∧ wk * xk ≤ xk`. So no single term
can exceed the magnitude of its input — the exact-integer analogue of the
sup-norm bound, here with tolerance identically `0` because each term *equals* one
of the three endpoints.

Proof: case-split on the three weight values (`ternary_dot_exact` pins the term to
`-xk`, `0`, or `xk`), then each bound is a cookbook `Int` fact —
`Int.neg_le_self` / `Int.le_refl` / `Int.neg_nonpos_of_nonneg` chained through
`Int.neg_le_neg`. No `omega`, no `decide` on the open `xk`. -/
theorem ternary_contribution_bounded {wk xk : Int}
    (hw : wk = -1 ∨ wk = 0 ∨ wk = 1) (hx : 0 ≤ xk) :
    -xk ≤ wk * xk ∧ wk * xk ≤ xk := by
  -- `-xk ≤ 0 ≤ xk` are the workhorse facts for the endpoints.
  have hnegle : -xk ≤ xk := Int.le_trans (Int.neg_nonpos_of_nonneg hx) hx
  have hnegle0 : -xk ≤ 0 := Int.neg_nonpos_of_nonneg hx
  match hw with
  | Or.inl hneg =>
      -- wk * xk = -xk
      have e : wk * xk = -xk := by rw [hneg]; exact Int.neg_one_mul xk
      exact ⟨by rw [e]; exact Int.le_refl (-xk), by rw [e]; exact hnegle⟩
  | Or.inr (Or.inl hzero) =>
      -- wk * xk = 0
      have e : wk * xk = 0 := by rw [hzero]; exact Int.zero_mul xk
      exact ⟨by rw [e]; exact hnegle0, by rw [e]; exact hx⟩
  | Or.inr (Or.inr hpos) =>
      -- wk * xk = xk
      have e : wk * xk = xk := by rw [hpos]; exact Int.one_mul xk
      exact ⟨by rw [e]; exact hnegle, by rw [e]; exact Int.le_refl xk⟩

-- ═══════════════════════════════════════════════════════════════════════
-- §4  Concrete worked example (a Fin 3 ternary matvec row, exact)
-- ═══════════════════════════════════════════════════════════════════════

/-! Input `x = [4, 2, 7]`, ternary weight row `w = [1, 0, -1]`. The exact dot is
`1*4 + 0*2 + (-1)*7 = 4 + 0 - 7 = -3`, with NO error term — `dot w x = -3` holds
by `decide` on the closed integer computation. The weight row satisfies
`IsTernary`. -/

/-- Worked input vector `[4, 2, 7]`. Out-of-range arm refuted Init-only
(`3 ≤ k + 3`), not by `omega`/`decide` on the open index. -/
def exX : Fin 3 → Int := fun k => match k with
  | ⟨0, _⟩ => 4
  | ⟨1, _⟩ => 2
  | ⟨2, _⟩ => 7
  | ⟨_ + 3, h⟩ => absurd h (Nat.not_lt_of_le (Nat.le_add_left 3 _))

/-- Worked ternary weight row `[1, 0, -1]`. -/
def exW : Fin 3 → Int := fun k => match k with
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => 0
  | ⟨2, _⟩ => -1
  | ⟨_ + 3, h⟩ => absurd h (Nat.not_lt_of_le (Nat.le_add_left 3 _))

/-- The worked weight row is ternary: each entry is `-1`, `0`, or `+1`. -/
theorem exW_ternary : IsTernary exW := by
  intro k
  match k with
  | ⟨0, _⟩ => exact Or.inr (Or.inr rfl)
  | ⟨1, _⟩ => exact Or.inr (Or.inl rfl)
  | ⟨2, _⟩ => exact Or.inl rfl

/-- **The worked serve, exact.** `dot exW exX = -3` (`= 4 + 0 - 7`), proved by
`decide` on the fully closed integer computation — no tolerance, no error term.
This is the ground-truth contrast to the quantized worked examples, which only
land *within* `tau`. -/
theorem ex_dot_exact : dot exW exX = -3 := by decide

-- ═══════════════════════════════════════════════════════════════════════
-- §5  The kernel-meaning bridge: exact ⇒ τ = 0 argmax (no margin needed)
-- ═══════════════════════════════════════════════════════════════════════

/--
**Exactness ⇒ the `τ = 0` corner of the quant certificate.** Because the ternary
matvec is exact, its computed output logit vector `Lc` *equals* the specification
`Ls` (zero error term). So no half-margin slack is needed: the computed argmax is
the spec argmax with ZERO tolerance — trivially, since the two vectors are equal.
This instantiates the `tau = 0` boundary of
`QuantMatvecAdmissibility` / `QualityMarginCacheAdmissibility`: where a quantized
kernel needs `2 * tau ≤ gamma` to preserve the token, an exact kernel needs no
margin at all. One-liner: rewrite the equality and reuse the hypothesis. -/
theorem exact_kernel_argmax_preserved {n : Nat} (Lc Ls : Fin n → Int)
    (hexact : Lc = Ls) (i : Fin n) (hspec : IsStrictArgmax Ls i) :
    IsStrictArgmax Lc i := by
  rw [hexact]; exact hspec

/--
**Exact-kernel admissibility needs no tolerance.** The computed output and the
spec share the SAME strict argmax whenever they are equal — the `tau = 0` reading
of admissibility. There is no `2 * tau ≤ gamma` premise because the gap is
identically zero. The predicted token is the spec's predicted token, with no
margin budget consumed. -/
theorem exact_kernel_token_preserved {n : Nat} (Lc Ls : Fin n → Int)
    (hexact : Lc = Ls) (i : Fin n) (hspec : IsStrictArgmax Ls i) :
    IsStrictArgmax Lc i ∧ IsStrictArgmax Ls i :=
  ⟨exact_kernel_argmax_preserved Lc Ls hexact i hspec, hspec⟩

end TernaryMatvecExact
end Aether
end Gnosis
