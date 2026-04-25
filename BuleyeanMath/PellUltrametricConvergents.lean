import Init

/-!
# Pell Convergents Meet the 2-adic Valuation

Bridge between two existing modules:

- `PellCatLucasTraceFamily.lean` records the Pell recurrence `(s, d) = (2, -1)`
  with **discriminant** `Δ = s² - 4 d = 8 = 2³`. The 2-adic valuation is
  the natural "archon" for Pell arithmetic: the only prime dividing `Δ`.
- `UltrametricBufferInstance.lean` exposes the valuation surrogate
  `vp p n : ℕ` (with sentinel `vp p 0 = 1000`) and the strong triangle
  inequality witness on integer differences.
- `ContinuedFractionConvergents.lean` computes the Pell convergents of
  `√2 = [1; 2, 2, 2, ...]`: `(1,1), (3,2), (7,5), (17,12), (41,29),
  (99,70), (239,169), (577,408)`.

This module **witnesses** a structural pattern in the 2-adic valuation of
Pell convergent denominators `q_n` and closes the Pell identity
`p_n² − 2 q_n² = ±1` modulo `8`.

## What this module witnesses

1. Inline `vp` (2-adic valuation surrogate). Sanity checks at small
   powers of `2`.
2. Inline Pell CF convergent computation. The first eight Pell
   convergents match the textbook.
3. Tabulate `v_2(p_n)` and `v_2(q_n)` for `n = 0..7`:
   `(1,1) ↦ (0,0)`, `(3,2) ↦ (0,1)`, `(7,5) ↦ (0,0)`,
   `(17,12) ↦ (0,2)`, `(41,29) ↦ (0,0)`, `(99,70) ↦ (0,1)`,
   `(239,169) ↦ (0,0)`, `(577,408) ↦ (0,3)`.
4. **Pell numerators are odd**: `v_2(p_n) = 0` for `n = 0..7`.
5. **Ruler-sequence pattern** on denominators: `v_2(q_n) = v_2(n + 1)`
   at every computed point `n = 0..7`. Matches the 2-adic ruler
   sequence `0, 1, 0, 2, 0, 1, 0, 3, ...`.
6. **Pell identity mod 8**: for `n = 0..5`,
   `(p_n² − 2 q_n²) mod 8 ∈ {1, 7}` (i.e., `±1 mod 8`), with the sign
   alternating as `(-1)^n`. Consistent with `p_n² ≡ 1 mod 8` (odd squares)
   and `2 q_n² mod 8 ∈ {0, 2}` depending on `v_2(q_n)`.
7. **Ultrametric on Pell denominators**: one triple-of-`q_n` witness
   `min(v_2(q_a − q_b), v_2(q_b − q_c)) ≤ v_2(q_a − q_c)` via the same
   inequality used in `UltrametricBufferInstance`.
8. `pell_ultrametric_witness`: one theorem bundling (4), (5), (6), (7).

## What this module does *not* claim

- `v_2(q_n) = v_2(n + 1)` is observed at `n = 0..7`, not proved for
  all `n`. A general proof would require an inductive argument on the
  Pell recurrence `q_{n+1} = 2 q_n + q_{n-1}` combined with a lift
  of `vp` from the `Init`-only surrogate to a genuine `p`-adic
  valuation.
- `vp` is a finite-Nat valuation surrogate. It is not the `p`-adic
  absolute value on `ℚ_p`, not the image of `padicValNat`, and has
  a sentinel `1000` standing in for `+∞` at `0`. No `ℤ_2` completion
  appears anywhere here.
- The "Pell identity mod 8" item closes the ambient integer identity
  `p² − 2q² = ±1` at the residue level modulo `8`; it does not
  derive that identity from anything deeper.
- Ultrametric strong triangle inequality is witnessed on one triple
  of Pell denominators, not on all triples.

No `sorry`, no new `axiom`, `Init`-only. Every numerical item closes
by kernel `decide`.
-/

namespace BuleyeanMath
namespace PellUltrametricConvergents

/-! ## 2-adic valuation surrogate (inlined from `UltrametricBufferInstance`) -/

/-- Sentinel standing in for `v_2(0) = +∞`; chosen large enough to
dominate every `v_2(n)` we compute. -/
def sentinel : Nat := 1000

/-- Auxiliary `p`-adic valuation with explicit fuel. Mirrors
`UltrametricBufferInstance.vpAux`; inlined to keep this module
self-contained at the `Init` level. -/
def vpAux (p : Nat) : Nat → Nat → Nat
  | 0,         _        => sentinel
  | _,         0        => 0
  | Nat.succ m, Nat.succ k =>
    let n := Nat.succ m
    if p ≤ 1 then 0
    else if n % p = 0 then 1 + vpAux p (n / p) k
    else 0

/-- `p`-adic valuation of a natural number, with `v_p(0) = sentinel`. -/
def vp (p n : Nat) : Nat := vpAux p n n

/-- 2-adic valuation `v_2 : Nat → Nat`. -/
def v2 (n : Nat) : Nat := vp 2 n

/-- Natural-number surrogate for `v_2(|x − y|)` on integer arguments. -/
def v2Diff (x y : Int) : Nat := vp 2 (x - y).natAbs

/-! ### Sanity checks on `v2` -/

example : v2 1 = 0 := by decide
example : v2 2 = 1 := by decide
example : v2 4 = 2 := by decide
example : v2 8 = 3 := by decide
example : v2 16 = 4 := by decide
example : v2 0 = sentinel := by decide

/-! ## Pell convergents (inlined from `ContinuedFractionConvergents`)

The `√2` continued fraction is `[1; 2, 2, 2, ...]`. We compute the first
eight convergents as a `List (Nat × Nat)`. -/

/-- One step of the convergent recurrence. -/
def stepConvergent (prev2 prev1 : Nat × Nat) (a : Nat) : Nat × Nat :=
  (a * prev1.1 + prev2.1, a * prev1.2 + prev2.2)

/-- Tail-recursive accumulator for convergents. -/
def convergentsAux : Nat × Nat → Nat × Nat → List Nat → List (Nat × Nat)
  | _,     _,     []      => []
  | prev2, prev1, a :: as =>
    let curr := stepConvergent prev2 prev1 a
    curr :: convergentsAux prev1 curr as

/-- Convergents of a simple continued fraction from its partial-quotient
list. Returns the list of `(p_n, q_n)` pairs. -/
def convergents (as : List Nat) : List (Nat × Nat) :=
  convergentsAux (0, 1) (1, 0) as

/-- The first eight convergents of `√2 = [1; 2, 2, 2, 2, 2, 2, 2]` are
`1/1, 3/2, 7/5, 17/12, 41/29, 99/70, 239/169, 577/408`. -/
theorem sqrt2_convergents_8 :
    convergents [1, 2, 2, 2, 2, 2, 2, 2]
      = [(1, 1), (3, 2), (7, 5), (17, 12),
         (41, 29), (99, 70), (239, 169), (577, 408)] := by decide

/-- The eight Pell convergents as a fixed list, for downstream reuse. -/
def pellConvergents : List (Nat × Nat) :=
  [(1, 1), (3, 2), (7, 5), (17, 12),
   (41, 29), (99, 70), (239, 169), (577, 408)]

/-- `pellConvergents` matches the CF computation. -/
theorem pellConvergents_eq :
    pellConvergents = convergents [1, 2, 2, 2, 2, 2, 2, 2] := by decide

/-! ## 2-adic valuation of Pell numerators and denominators

Compute `v_2(p_n)` and `v_2(q_n)` at `n = 0..7`. The numerators are all
odd (`v_2 = 0`); the denominators trace the ruler sequence. -/

/-- `v_2` applied to a Pell numerator/denominator pair. -/
def v2Pair (pq : Nat × Nat) : Nat × Nat := (v2 pq.1, v2 pq.2)

/-- Valuation table on the first eight Pell convergents. -/
theorem v2_pell_table :
    v2Pair (1,   1)   = (0, 0) ∧
    v2Pair (3,   2)   = (0, 1) ∧
    v2Pair (7,   5)   = (0, 0) ∧
    v2Pair (17,  12)  = (0, 2) ∧
    v2Pair (41,  29)  = (0, 0) ∧
    v2Pair (99,  70)  = (0, 1) ∧
    v2Pair (239, 169) = (0, 0) ∧
    v2Pair (577, 408) = (0, 3) := by decide

/-! ## Observation 1: Pell numerators are odd

For `n = 0..7`, `v_2(p_n) = 0`. Classical fact: `p_n² − 2 q_n² = ±1`
forces `p_n` odd (even `p_n` would give `0 − 2 q_n² = ±1 mod 2`,
impossible). Here it is witnessed pointwise. -/

/-- `v_2(p_n) = 0` for every Pell numerator `n = 0..7`. -/
theorem pell_numerators_odd :
    v2 1 = 0 ∧ v2 3 = 0 ∧ v2 7 = 0 ∧ v2 17 = 0 ∧
    v2 41 = 0 ∧ v2 99 = 0 ∧ v2 239 = 0 ∧ v2 577 = 0 := by decide

/-! ## Observation 2: denominators follow the 2-adic ruler

The ruler sequence `r(m) := v_2(m)` at `m = 1, 2, 3, 4, 5, 6, 7, 8` is
`0, 1, 0, 2, 0, 1, 0, 3`. Pell denominators `q_n` for `n = 0..7` give
`1, 2, 5, 12, 29, 70, 169, 408`, with `v_2` values `0, 1, 0, 2, 0, 1,
0, 3` — the same pattern, shifted by one: `v_2(q_n) = v_2(n + 1)`. -/

/-- `v_2(q_n) = v_2(n + 1)` at `n = 0..7`. Witnessed pointwise. -/
theorem pell_denominators_ruler :
    v2 1   = v2 1 ∧  -- n = 0: q_0 = 1,   v_2(1) = v_2(0 + 1)
    v2 2   = v2 2 ∧  -- n = 1: q_1 = 2,   v_2(2) = v_2(1 + 1)
    v2 5   = v2 3 ∧  -- n = 2: q_2 = 5,   v_2(5) = v_2(2 + 1) = 0
    v2 12  = v2 4 ∧  -- n = 3: q_3 = 12,  v_2(12) = v_2(3 + 1) = 2
    v2 29  = v2 5 ∧  -- n = 4: q_4 = 29,  v_2(29) = v_2(4 + 1) = 0
    v2 70  = v2 6 ∧  -- n = 5: q_5 = 70,  v_2(70) = v_2(5 + 1) = 1
    v2 169 = v2 7 ∧  -- n = 6: q_6 = 169, v_2(169) = v_2(6 + 1) = 0
    v2 408 = v2 8    -- n = 7: q_7 = 408, v_2(408) = v_2(7 + 1) = 3
    := by decide

/-- The explicit ruler pattern values themselves:
`v_2(q_n)` for `n = 0..7` equals `0, 1, 0, 2, 0, 1, 0, 3`. -/
theorem pell_denominators_ruler_values :
    v2 1   = 0 ∧ v2 2   = 1 ∧ v2 5   = 0 ∧ v2 12  = 2 ∧
    v2 29  = 0 ∧ v2 70  = 1 ∧ v2 169 = 0 ∧ v2 408 = 3 := by decide

/-! ## Observation 3: Pell identity modulo 8

For the Pell convergents `p_n² − 2 q_n² = ±1`, alternating `−, +, −, +,
...` from `n = 0`. Reducing modulo `8`:

- `p_n` is odd (Observation 1), so `p_n² ≡ 1 mod 8`.
- `2 q_n² mod 8` depends on `v_2(q_n)`:
  - `v_2(q_n) = 0` (q odd) ⇒ `q² ≡ 1 mod 8` ⇒ `2 q² ≡ 2 mod 8`.
  - `v_2(q_n) ≥ 1` ⇒ `q² ≡ 0 mod 4` ⇒ `2 q² ≡ 0 mod 8`.

We compute `(p² − 2 q²) mod 8` at `n = 0..5`. Expected values:

- `n = 0`: `1 − 2 · 1 = -1 ≡ 7 mod 8`.
- `n = 1`: `9 − 2 · 4 = 1 ≡ 1 mod 8`.
- `n = 2`: `49 − 2 · 25 = -1 ≡ 7 mod 8`.
- `n = 3`: `289 − 2 · 144 = 1 ≡ 1 mod 8`.
- `n = 4`: `1681 − 2 · 841 = -1 ≡ 7 mod 8`.
- `n = 5`: `9801 − 2 · 4900 = 1 ≡ 1 mod 8`.

We work in `Int` with `Int.emod`, which returns a non-negative residue
for positive modulus. -/

/-- Signed Pell identity value `p² − 2 q²` as `Int`. -/
def pellValue (pq : Nat × Nat) : Int :=
  (Int.ofNat (pq.1 * pq.1)) - 2 * (Int.ofNat (pq.2 * pq.2))

/-- Pell identity reduced modulo `8` at `n = 0..5`: alternates `7, 1`.
`7 ≡ -1 mod 8` and `1 ≡ +1 mod 8`, so this closes the sign pattern
`−, +, −, +, −, +` at the residue level. -/
theorem pell_identity_mod_8 :
    pellValue (1, 1)    % 8 = 7 ∧
    pellValue (3, 2)    % 8 = 1 ∧
    pellValue (7, 5)    % 8 = 7 ∧
    pellValue (17, 12)  % 8 = 1 ∧
    pellValue (41, 29)  % 8 = 7 ∧
    pellValue (99, 70)  % 8 = 1 := by decide

/-- Raw signed values at `n = 0..5`: `−1, +1, −1, +1, −1, +1`. -/
theorem pell_identity_signed :
    pellValue (1, 1)    = -1 ∧
    pellValue (3, 2)    =  1 ∧
    pellValue (7, 5)    = -1 ∧
    pellValue (17, 12)  =  1 ∧
    pellValue (41, 29)  = -1 ∧
    pellValue (99, 70)  =  1 := by decide

/-! ## Observation 4: ultrametric on Pell denominators

Pell denominators `q_n = 1, 2, 5, 12, 29, 70, 169, 408`. We witness
the strong triangle inequality `min(v_2(q_a − q_b), v_2(q_b − q_c)) ≤
v_2(q_a − q_c)` on representative triples, matching the schema of
`UltrametricBufferInstance.ultrametricHolds`. -/

/-- Ultrametric witness on an integer triple under `p = 2`. -/
abbrev ultrametric2 (x y z : Int) : Prop :=
  min (v2Diff x y) (v2Diff y z) ≤ v2Diff x z

/-- Triple `(q_0, q_1, q_3) = (1, 2, 12)` under `p = 2`:
differences `|1 − 2| = 1`, `|2 − 12| = 10`, `|1 − 12| = 11`; valuations
`v_2(1) = 0`, `v_2(10) = 1`, `v_2(11) = 0`; `min(0, 1) = 0 ≤ 0`. -/
theorem ultrametric_pell_q0_q1_q3 :
    ultrametric2 1 2 12 := by decide

/-- Triple `(q_1, q_3, q_7) = (2, 12, 408)` under `p = 2`:
differences `|2 − 12| = 10`, `|12 − 408| = 396`, `|2 − 408| = 406`;
valuations `v_2(10) = 1`, `v_2(396) = 2`, `v_2(406) = 1`;
`min(1, 2) = 1 ≤ 1`. Equality on the bound — isosceles case. -/
theorem ultrametric_pell_q1_q3_q7 :
    ultrametric2 2 12 408 := by decide

/-- Triple `(q_0, q_3, q_7) = (1, 12, 408)` under `p = 2`:
differences `|1 − 12| = 11`, `|12 − 408| = 396`, `|1 − 408| = 407`;
valuations `v_2(11) = 0`, `v_2(396) = 2`, `v_2(407) = 0`;
`min(0, 2) = 0 ≤ 0`. -/
theorem ultrametric_pell_q0_q3_q7 :
    ultrametric2 1 12 408 := by decide

/-! ## Explicit difference valuations used in the triple witnesses

Recorded so downstream readers can see the raw numbers without
recomputing. -/

/-- Valuations of the pairwise differences for `(1, 2, 12)`. -/
theorem v2_diffs_q0_q1_q3 :
    v2Diff 1 2   = 0 ∧
    v2Diff 2 12  = 1 ∧
    v2Diff 1 12  = 0 := by decide

/-- Valuations of the pairwise differences for `(2, 12, 408)`. -/
theorem v2_diffs_q1_q3_q7 :
    v2Diff 2 12    = 1 ∧
    v2Diff 12 408  = 2 ∧
    v2Diff 2 408   = 1 := by decide

/-! ## Bridge theorem

One labelled conjunction combining: Pell numerators odd, ruler pattern
on denominators, Pell identity modulo `8`, and an ultrametric triple
on Pell denominators. This is the citeable anchor for the Pell ↔
2-adic bridge. -/

/-- Master witness combining the four observations:
1. `v_2(p_n) = 0` for `n = 0..7` (numerators odd).
2. `v_2(q_n) = v_2(n + 1)` for `n = 0..7` (ruler sequence).
3. `p_n² − 2 q_n² ≡ ±1 mod 8`, alternating sign, for `n = 0..5`.
4. Strong triangle inequality on the Pell denominator triple
   `(q_1, q_3, q_7) = (2, 12, 408)`. -/
theorem pell_ultrametric_witness :
    -- 1. numerators odd
    (v2 1 = 0 ∧ v2 3 = 0 ∧ v2 7 = 0 ∧ v2 17 = 0 ∧
     v2 41 = 0 ∧ v2 99 = 0 ∧ v2 239 = 0 ∧ v2 577 = 0) ∧
    -- 2. ruler pattern v_2(q_n) = v_2(n + 1)
    (v2 1 = v2 1 ∧ v2 2 = v2 2 ∧ v2 5 = v2 3 ∧ v2 12 = v2 4 ∧
     v2 29 = v2 5 ∧ v2 70 = v2 6 ∧ v2 169 = v2 7 ∧ v2 408 = v2 8) ∧
    -- 2'. the ruler values explicitly
    (v2 1 = 0 ∧ v2 2 = 1 ∧ v2 5 = 0 ∧ v2 12 = 2 ∧
     v2 29 = 0 ∧ v2 70 = 1 ∧ v2 169 = 0 ∧ v2 408 = 3) ∧
    -- 3. Pell identity mod 8
    (pellValue (1, 1)   % 8 = 7 ∧
     pellValue (3, 2)   % 8 = 1 ∧
     pellValue (7, 5)   % 8 = 7 ∧
     pellValue (17, 12) % 8 = 1 ∧
     pellValue (41, 29) % 8 = 7 ∧
     pellValue (99, 70) % 8 = 1) ∧
    -- 4. ultrametric on a Pell denominator triple
    ultrametric2 2 12 408 := by decide

end PellUltrametricConvergents
end BuleyeanMath
