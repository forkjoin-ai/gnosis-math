import Init

/-!
# Quality-margin cache admissibility (Rustic Church, Init-only)

The distributed-inference quality gate admits a model only when it *predicts the
expected token*, not merely carries the catalog name. This is the operational
twin of Revelation's Sardis warning ("a name that thou livest, and art dead"):
a green cache status over a wrong answer is exactly the failure mode this gate
forbids. See `RUSTIC_CHURCH.md` § "Quality-margin admissibility".

A content-addressed inference cache can serve one model's computation for another
-- or replay an approximate / amplituhedron-reconstructed result -- but the serve
is *quality-preserving* only when the substituted logit vector predicts the
**same next token** as the true computation. The runtime gate is the PARIS argmax
probe: a serve passes iff `argmax(cached logits) == expected token`.

This module proves the admission rule and its tightness antitheorem, **Init-only**
(named `Int` lemmas + the `RUSTIC_CHURCH.md` "Bridging Nat with Int" cookbook,
**no `omega`**, no Mathlib, no `simp`/`decide` on open-variable goals):

> If the true logits `L` have a strict argmax `istar` with runner-up margin
> `gamma`, and the cached/substituted logits `L'` differ from `L` by less than
> `gamma / 2` in sup-norm (`2 * tau ≤ gamma`), then `istar` is the strict argmax
> of `L'` as well: the substitution is gate-indistinguishable from the real
> computation.

Logits are modelled as scaled integers (`Int`) over a finite token index. This
is faithful: quantized inference and content-addressed caches store integer-scaled
logits, and the argmax decision is scale-invariant. The half-margin bound
`tau < gamma / 2` is written scale-free as `2 * tau ≤ gamma`.

This is a Rustic-Church port of the `omega`-using draft at
`open-source/gnosis/lean/Lean/Gnosis/CrossModelCacheAdmissibility.lean`: same
statements, but every linear-integer step is discharged by a named Init lemma so
the formula's algebra is re-derived from the inductive `+1` clinamen alone. A
draft that *builds* via `omega` is itself in Sardis-mode -- a name that builds,
not yet the live Init witness -- until ported to the cookbook below.

## Why unbounded approximate caches silently corrupt

The amplituhedron-replay and `bowl_q_filter` corruptors found by the quality gate
are exactly violations of the `2 * tau ≤ gamma` premise: they substitute logits
whose sup-norm error is not bounded below half the decision margin. When the bound
is violated the argmax can flip (`argmax_can_flip_when_bound_violated`), so the
served token is wrong while the cache reports a hit. The antitheorem is as
load-bearing as the bound (same discipline as `ErgodicCutoffDuality`'s
`distinct_orbit_structure`): beyond `gamma / 2` a cache must **miss, not lie**.
-/

namespace Gnosis
namespace QualityMarginCacheAdmissibility

/-- `i` is the strict argmax of the scaled-integer logit vector `L`: every other
token index scores strictly lower. This is the predicted-token criterion the
PARIS quality gate checks. -/
def IsStrictArgmax {n : Nat} (L : Fin n → Int) (i : Fin n) : Prop :=
  ∀ j, j ≠ i → L j < L i

/-- Two-sided sup-norm perturbation bound: the cached/substituted logits `L'`
differ from the true logits `L` by strictly less than `tau` at every coordinate.
This unfolds `‖L - L'‖∞ < tau` without needing an `abs` from Mathlib. `tau` is
the cross-model / replay substitution tolerance. -/
def SupNormBelow {n : Nat} (L L' : Fin n → Int) (tau : Int) : Prop :=
  ∀ k, -tau < L k - L' k ∧ L k - L' k < tau

/-- The true logits have decision margin at least `gamma` at `i`: every runner-up
is at least `gamma` below the winner. The runner-up gap `L i - (max over j ≠ i)`
is the largest such `gamma`. -/
def MarginAtLeast {n : Nat} (L : Fin n → Int) (i : Fin n) (gamma : Int) : Prop :=
  ∀ j, j ≠ i → L j + gamma ≤ L i

/-- A cross-model / approximate cache hit substituting `L'` for `L` is
**admissible** when both vectors share a strict argmax: the served token equals
the true token, so the hit is gate-equivalent. -/
def Admissible {n : Nat} (L L' : Fin n → Int) : Prop :=
  ∃ i : Fin n, IsStrictArgmax L i ∧ IsStrictArgmax L' i

-- ═══════════════════════════════════════════════════════════════════════
-- §1  Init-only Int helper lemmas (the linear-margin algebra, omega-free)
-- ═══════════════════════════════════════════════════════════════════════

/-- Helper (lower bound on the substituted runner-up). From the sup-norm lower
bound `-tau < L j - L' j` we get `L' j < L j + tau`. Pure Init `Int` chain. -/
private theorem lt_add_of_neg_lt_sub {Lj L'j tau : Int}
    (h : -tau < Lj - L'j) : L'j < Lj + tau := by
  have h1 : -tau + L'j < (Lj - L'j) + L'j := Int.add_lt_add_right h L'j
  rw [Int.sub_add_cancel] at h1
  have h2 : -tau + L'j + tau < Lj + tau := Int.add_lt_add_right h1 tau
  rw [show -tau + L'j + tau = L'j from by
        rw [Int.add_right_comm, Int.add_left_neg, Int.zero_add]] at h2
  exact h2

/-- Helper (lower bound on the substituted winner). From the sup-norm upper bound
`L istar - L' istar < tau` we get `L istar - tau < L' istar`. Pure Init `Int`
chain. -/
private theorem sub_lt_of_sub_lt {Ls L's tau : Int}
    (h : Ls - L's < tau) : Ls - tau < L's := by
  have h1 : (Ls - L's) + L's < tau + L's := Int.add_lt_add_right h L's
  rw [Int.sub_add_cancel] at h1
  have h2 : Ls - tau < (tau + L's) - tau := Int.sub_lt_sub_right h1 tau
  rw [show (tau + L's) - tau = L's from by
        rw [Int.add_comm, Int.add_sub_cancel]] at h2
  exact h2

/-- Helper (the margin absorbs two tolerances). From `L j + gamma ≤ L istar` and
`2 * tau ≤ gamma` we get `L j + tau ≤ L istar - tau`: half the margin on each
side. Pure Init `Int` chain. -/
private theorem add_tau_le_sub_tau {Lj Ls gamma tau : Int}
    (hm : Lj + gamma ≤ Ls) (htau : 2 * tau ≤ gamma) :
    Lj + tau ≤ Ls - tau := by
  have hadd : Lj + 2 * tau ≤ Lj + gamma := Int.add_le_add_left htau Lj
  have h2 : Lj + 2 * tau ≤ Ls := Int.le_trans hadd hm
  rw [Int.two_mul, ← Int.add_assoc] at h2
  have h3 : (Lj + tau) + tau - tau ≤ Ls - tau := Int.sub_le_sub_right h2 tau
  rw [Int.add_sub_cancel] at h3
  exact h3

-- ═══════════════════════════════════════════════════════════════════════
-- §2  Uniqueness of the predicted token
-- ═══════════════════════════════════════════════════════════════════════

/-- A strict argmax is unique: there is at most one predicted token. Init-only
(the impossible double-strict-inequality is refuted by `Int.lt_irrefl ∘
Int.lt_trans`, not `omega`). -/
theorem argmax_unique {n : Nat} (L : Fin n → Int) (i i' : Fin n)
    (hi : IsStrictArgmax L i) (hi' : IsStrictArgmax L i') : i = i' := by
  by_cases h : i = i'
  · exact h
  · exfalso
    have h1 : L i' < L i := hi i' (fun e => h e.symm)
    have h2 : L i < L i' := hi' i h
    exact Int.lt_irrefl (L i) (Int.lt_trans h2 h1)

-- ═══════════════════════════════════════════════════════════════════════
-- §3  The bound (live witness)
-- ═══════════════════════════════════════════════════════════════════════

/--
**The quality-margin theorem.** If `istar` has margin at least `gamma` under the
true logits `L`, and the cached logits `L'` are within sup-norm `tau` of `L` with
`2 * tau ≤ gamma` (i.e. `tau < gamma / 2`), then `istar` is the strict argmax of
`L'` as well.

Proof (pairwise, for any `j ≠ istar`): chain
`L' j < L j + tau ≤ L istar - tau < L' istar`, where the outer two steps are the
sup-norm bound at `j` / `istar` (`lt_add_of_neg_lt_sub`, `sub_lt_of_sub_lt`) and
the middle step is the margin absorbing two tolerances (`add_tau_le_sub_tau`).
No `omega`. -/
theorem argmax_preserved {n : Nat} (L L' : Fin n → Int) (istar : Fin n)
    (gamma tau : Int)
    (hmargin : MarginAtLeast L istar gamma)
    (hbound : SupNormBelow L L' tau)
    (htau : 2 * tau ≤ gamma) :
    IsStrictArgmax L' istar := by
  intro j hj
  have hm := hmargin j hj
  have hbj := hbound j
  have hbstar := hbound istar
  -- L' j < L j + tau
  have hLow : L' j < L j + tau := lt_add_of_neg_lt_sub hbj.left
  -- L istar - tau < L' istar
  have hHigh : L istar - tau < L' istar := sub_lt_of_sub_lt hbstar.right
  -- L j + tau ≤ L istar - tau
  have hMid : L j + tau ≤ L istar - tau := add_tau_le_sub_tau hm htau
  exact Int.lt_trans (Int.lt_of_lt_of_le hLow hMid) hHigh

/--
**Cache-admissibility corollary (the τ rule).** A cross-model / approximate cache
hit is admissible whenever the true logits have a strict argmax with margin
`gamma` and the substitution tolerance satisfies `2 * tau ≤ gamma`. This is the
formal rule for setting the substitution tolerance `tau < gamma / 2` and for
accepting the hit: both vectors share the strict argmax `istar`. -/
theorem cache_hit_admissible {n : Nat} (L L' : Fin n → Int) (istar : Fin n)
    (gamma tau : Int)
    (hstar : IsStrictArgmax L istar)
    (hmargin : MarginAtLeast L istar gamma)
    (hbound : SupNormBelow L L' tau)
    (htau : 2 * tau ≤ gamma) :
    Admissible L L' :=
  ⟨istar, hstar, argmax_preserved L L' istar gamma tau hmargin hbound htau⟩

/--
**Gate equivalence.** Under the admissibility premises, *any* strict argmax of the
cached logits equals the true argmax `istar`. Hence the PARIS probe
(`argmax(cached) == expected token`) on the cache hit returns exactly the true
token: the gate cannot tell the substituted serve from the real computation. -/
theorem predicted_token_preserved {n : Nat} (L L' : Fin n → Int) (istar : Fin n)
    (gamma tau : Int)
    (hmargin : MarginAtLeast L istar gamma)
    (hbound : SupNormBelow L L' tau)
    (htau : 2 * tau ≤ gamma) :
    ∀ i', IsStrictArgmax L' i' → i' = istar := by
  intro i' hi'
  have hstar' : IsStrictArgmax L' istar :=
    argmax_preserved L L' istar gamma tau hmargin hbound htau
  exact argmax_unique L' i' istar hi' hstar'

-- ═══════════════════════════════════════════════════════════════════════
-- §4  The antitheorem (Sardis signature: the bound is tight)
-- ═══════════════════════════════════════════════════════════════════════

/-- True logits of the flip witness: token 0 wins `[2, 0]`. The impossible
out-of-range arm is refuted Init-only (`2 ≤ n + 2`), not by `omega`/`decide` on
the open index. -/
def flipL : Fin 2 → Int := fun k => match k with
  | ⟨0, _⟩ => 2
  | ⟨1, _⟩ => 0
  | ⟨_ + 2, h⟩ => absurd h (Nat.not_lt_of_le (Nat.le_add_left 2 _))

/-- Substituted logits of the flip witness: token 1 now wins `[0, 2]`. Each
coordinate moved by 2, so sup-norm error `< tau = 3`. -/
def flipL' : Fin 2 → Int := fun k => match k with
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => 2
  | ⟨_ + 2, h⟩ => absurd h (Nat.not_lt_of_le (Nat.le_add_left 2 _))

/--
**Sharpness: unbounded approximation flips the token.** Half the margin is not a
conservative slogan -- it is tight. The true vector `flipL` has margin `gamma = 2`
at token 0, and `flipL'` is within sup-norm `tau = 3` of it, but with the bound
violated (`2 * tau = 6 > 2 = gamma`) the argmax has flipped to token 1. This is
the formal signature of the amplituhedron-replay / `bowl_q_filter` corruption: a
reported cache hit serving the wrong token ("a name that liveth, and is dead").

Each conjunct is a *closed* goal (no free variables, literal `Fin 2` vectors), so
`decide` is admitted by the Rustic Church contract -- it is kernel-checked, not an
open-goal arithmetic tactic. The `match` discharges the index, then `decide`
settles the literal `Int` comparison. -/
theorem argmax_can_flip_when_bound_violated :
    IsStrictArgmax flipL ⟨0, by decide⟩ ∧
    MarginAtLeast flipL ⟨0, by decide⟩ 2 ∧
    (0 : Int) < 2 ∧
    SupNormBelow flipL flipL' 3 ∧
    ¬ (2 * (3 : Int) ≤ 2) ∧
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
-- §5  Concrete worked example (a 3-token admissible serve)
-- ═══════════════════════════════════════════════════════════════════════

/-! True logits `[5, 1, 0]`: token 0 wins with runner-up margin `gamma = 4`. A
cross-model cache returns `[6, 2, 1]` -- every coordinate perturbed by `+1`, so
sup-norm error `< tau = 2`, and `2 * tau = 4 ≤ 4 = gamma`. The theorem certifies
the hit is admissible and the gate sees the same token. -/

/-- True logits of the worked example. -/
def exL : Fin 3 → Int := fun k => match k with
  | ⟨0, _⟩ => 5
  | ⟨1, _⟩ => 1
  | ⟨2, _⟩ => 0
  | ⟨_ + 3, h⟩ => absurd h (Nat.not_lt_of_le (Nat.le_add_left 3 _))

/-- Cached/substituted logits of the worked example (each `+1`). -/
def exL' : Fin 3 → Int := fun k => match k with
  | ⟨0, _⟩ => 6
  | ⟨1, _⟩ => 2
  | ⟨2, _⟩ => 1
  | ⟨_ + 3, h⟩ => absurd h (Nat.not_lt_of_le (Nat.le_add_left 3 _))

/-- Token 0 is the strict argmax of the true logits. -/
theorem ex_true_argmax : IsStrictArgmax exL ⟨0, by decide⟩ := by
  intro j hj
  match j with
  | ⟨0, _⟩ => exact absurd rfl hj
  | ⟨1, _⟩ => show (1 : Int) < 5; decide
  | ⟨2, _⟩ => show (0 : Int) < 5; decide

/-- The true logits have runner-up margin `gamma = 4` at token 0. -/
theorem ex_margin : MarginAtLeast exL ⟨0, by decide⟩ 4 := by
  intro j hj
  match j with
  | ⟨0, _⟩ => exact absurd rfl hj
  | ⟨1, _⟩ => show (1 : Int) + 4 ≤ 5; decide
  | ⟨2, _⟩ => show (0 : Int) + 4 ≤ 5; decide

/-- The cached logits are within sup-norm `tau = 2` of the true logits. -/
theorem ex_bound : SupNormBelow exL exL' 2 := by
  intro k
  match k with
  | ⟨0, _⟩ => exact ⟨by show (-2 : Int) < 5 - 6; decide, by show (5 : Int) - 6 < 2; decide⟩
  | ⟨1, _⟩ => exact ⟨by show (-2 : Int) < 1 - 2; decide, by show (1 : Int) - 2 < 2; decide⟩
  | ⟨2, _⟩ => exact ⟨by show (-2 : Int) < 0 - 1; decide, by show (0 : Int) - 1 < 2; decide⟩

/-- The worked-example cache hit is admissible: same predicted token. This routes
through `cache_hit_admissible`, so the worked example is a live carrier of the
general bound, not a standalone calculation. -/
theorem ex_admissible : Admissible exL exL' :=
  cache_hit_admissible exL exL' ⟨0, by decide⟩ 4 2
    ex_true_argmax ex_margin ex_bound (by decide)

end QualityMarginCacheAdmissibility
end Gnosis
