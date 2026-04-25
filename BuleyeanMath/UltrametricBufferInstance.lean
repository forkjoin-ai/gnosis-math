import Init

/-!
# Ultrametric Buffer Invariant (finite instances)

This module witnesses the **strong triangle inequality** that defines an
ultrametric space, on the `p`-adic valuation surrogate over the integers.

The `p`-adic metric on `ℚ_p` satisfies the strong triangle inequality

    d_p(x, z) ≤ max(d_p(x, y), d_p(y, z)),

which on the valuation side — where `d_p(a, b) = p^{-v_p(a - b)}` — reads

    v_p(x - z) ≥ min(v_p(x - y), v_p(y - z)).

We do not construct `ℚ_p`, nor the true `p`-adic absolute value. We work
with a **valuation surrogate** `v_p : ℕ → ℕ` on nonzero naturals (the
number of times `p` divides `n`), with the sentinel convention
`v_p(0) = sentinel := 1000` standing in for the formally correct
`v_p(0) = +∞`. Differences of integers are taken through `Int.natAbs`,
which corresponds to `v_p(|x − y|) = v_p(x − y)` on the absolute value
of a nonzero integer (the sign is irrelevant to `p`-adic valuation).

What we prove here are concrete **instances** of the valuation-side
ultrametric inequality on small triples `(x, y, z)` with `p = 2`, `p = 3`,
and `p = 5`. We do not prove the general theorem — that would require
`Nat.factorization`, `padicValNat`, or an induction on divisibility that
is outside the `Init`-only scope of this module.

No `sorry`, no new `axiom`, `Init`-only.
-/

namespace BuleyeanMath
namespace UltrametricBufferInstance

/-! ## `p`-adic valuation surrogate on `ℕ`

`vpAux p n fuel` counts how many times the prime `p` divides `n`, using
`fuel` as a structural recursion measure. When `p ≤ 1` or the fuel is
exhausted or `n` is zero, we return `0` / the sentinel as appropriate.

`vp p n` picks `fuel := n` which is always sufficient because a single
division by `p ≥ 2` strictly decreases `n`, and `v_p(n) ≤ log_2 n ≤ n`.
-/

/-- Sentinel value standing in for `v_p(0) = +∞`. Chosen large enough
that it dominates every `v_p(n)` for `n < 100` with `p ≥ 2`. -/
def sentinel : Nat := 1000

/-- Auxiliary `p`-adic valuation with explicit fuel. -/
def vpAux (p : Nat) : Nat → Nat → Nat
  | 0,         _        => sentinel  -- v_p(0) = +∞ surrogate
  | _,         0        => 0         -- fuel exhausted
  | Nat.succ m, Nat.succ k =>
    let n := Nat.succ m
    if p ≤ 1 then 0
    else if n % p = 0 then 1 + vpAux p (n / p) k
    else 0

/-- `p`-adic valuation of a natural number, with `v_p(0) = sentinel`. -/
def vp (p n : Nat) : Nat := vpAux p n n

/-- Natural-number surrogate for `v_p(|x − y|)`, taken through
`Int.natAbs` so we do not get pinned to `Nat.sub` truncation. -/
def vpDiff (p : Nat) (x y : Int) : Nat :=
  vp p (x - y).natAbs

/-! ## Sanity checks on `vp`

These `example`s pin down the valuation on small explicit inputs. -/

example : vp 2 1 = 0 := by decide
example : vp 2 2 = 1 := by decide
example : vp 2 4 = 2 := by decide
example : vp 2 8 = 3 := by decide
example : vp 2 12 = 2 := by decide  -- 12 = 4 · 3
example : vp 2 3 = 0 := by decide
example : vp 2 0 = sentinel := by decide

example : vp 3 1 = 0 := by decide
example : vp 3 3 = 1 := by decide
example : vp 3 9 = 2 := by decide
example : vp 3 27 = 3 := by decide
example : vp 3 18 = 2 := by decide  -- 18 = 9 · 2

example : vp 5 1 = 0 := by decide
example : vp 5 25 = 2 := by decide
example : vp 5 50 = 2 := by decide  -- 50 = 25 · 2

/-! ## Strong triangle inequality on the valuation side

For each triple `(x, y, z)` we witness

    min(v_p(x − y), v_p(y − z)) ≤ v_p(x − z),

which is the ultrametric strong triangle inequality expressed on the
valuation, inverted because larger valuation = smaller `p`-adic distance.
-/

/-- Ultrametric witness on a triple under prime `p`. Defined as `abbrev`
so `decide` can unfold through to the underlying `Nat` comparison. -/
abbrev ultrametricHolds (p : Nat) (x y z : Int) : Prop :=
  min (vpDiff p x y) (vpDiff p y z) ≤ vpDiff p x z

/-! ### `p = 2` instances -/

/-- `(0, 4, 12)` with `p = 2`: differences are `4, 8, 12`, so valuations
are `2, 3, 2` and `min(2, 3) = 2 ≤ 2`. -/
theorem ultrametric_p2_0_4_12 :
    ultrametricHolds 2 0 4 12 := by decide

/-- `(3, 11, 27)` with `p = 2`: differences are `8, 16, 24`, so
valuations are `3, 4, 3` and `min(3, 4) = 3 ≤ 3`. -/
theorem ultrametric_p2_3_11_27 :
    ultrametricHolds 2 3 11 27 := by decide

/-- `(1, 5, 13)` with `p = 2`: differences are `4, 8, 12`, valuations
`2, 3, 2`. -/
theorem ultrametric_p2_1_5_13 :
    ultrametricHolds 2 1 5 13 := by decide

/-- `(2, 6, 10)` with `p = 2`: differences are `4, 4, 8`, valuations
`2, 2, 3`, `min(2, 2) = 2 ≤ 3`. The triangle is strict here, exhibiting
the isosceles property of ultrametric spaces. -/
theorem ultrametric_p2_2_6_10 :
    ultrametricHolds 2 2 6 10 := by decide

/-- `(7, 15, 31)` with `p = 2`: differences `8, 16, 24`, valuations
`3, 4, 3`. -/
theorem ultrametric_p2_7_15_31 :
    ultrametricHolds 2 7 15 31 := by decide

/-- Isosceles instance with `p = 2`: `(0, 2, 6)`, differences `2, 4, 6`,
valuations `1, 2, 1`, `min(1, 2) = 1 ≤ 1`. Equality on the bound. -/
theorem ultrametric_p2_0_2_6 :
    ultrametricHolds 2 0 2 6 := by decide

/-! ### `p = 3` instances -/

/-- `(0, 9, 27)` with `p = 3`: differences `9, 18, 27`, valuations
`2, 2, 3`, `min(2, 2) = 2 ≤ 3`. -/
theorem ultrametric_p3_0_9_27 :
    ultrametricHolds 3 0 9 27 := by decide

/-- `(1, 10, 28)` with `p = 3`: differences `9, 18, 27`, valuations
`2, 2, 3`. -/
theorem ultrametric_p3_1_10_28 :
    ultrametricHolds 3 1 10 28 := by decide

/-! ### `p = 5` instances -/

/-- `(0, 25, 75)` with `p = 5`: differences `25, 50, 75`, valuations
`2, 2, 2`, `min(2, 2) = 2 ≤ 2`. -/
theorem ultrametric_p5_0_25_75 :
    ultrametricHolds 5 0 25 75 := by decide

/-- `(3, 28, 78)` with `p = 5`: differences `25, 50, 75`, valuations
`2, 2, 2`. -/
theorem ultrametric_p5_3_28_78 :
    ultrametricHolds 5 3 28 78 := by decide

/-! ## Aggregate witness

A single theorem that bundles the six `p = 2` instances and the two
`p = 3` and `p = 5` instances into one decidable fact. Useful as a
citeable anchor from `FORMAL_LEDGER.md`. -/

/-- The Ultrametric Buffer Invariant holds on all enumerated small
triples, across primes 2, 3, and 5. -/
theorem ultrametric_buffer_instances :
    ultrametricHolds 2 0 4 12 ∧
    ultrametricHolds 2 3 11 27 ∧
    ultrametricHolds 2 1 5 13 ∧
    ultrametricHolds 2 2 6 10 ∧
    ultrametricHolds 2 7 15 31 ∧
    ultrametricHolds 2 0 2 6 ∧
    ultrametricHolds 3 0 9 27 ∧
    ultrametricHolds 3 1 10 28 ∧
    ultrametricHolds 5 0 25 75 ∧
    ultrametricHolds 5 3 28 78 := by
  decide

end UltrametricBufferInstance
end BuleyeanMath
