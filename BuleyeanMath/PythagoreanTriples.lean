import Init

/-!
# Pythagorean Triples via Euclid's Formula

Euclid's formula parametrizes a family of Pythagorean triples: for
positive integers `m > n`, the triple

    (a, b, c) = (m² - n², 2 m n, m² + n²)

witnesses `a² + b² = c²`. When additionally `gcd(m, n) = 1` and
`m, n` have opposite parity, the resulting triple is **primitive**
(pairwise coprime).

This module provides:

- `pythagTriple m n` computes the Euclid triple.
- `isPythag t` decides the Pythagorean condition `a² + b² = c²`.
- Concrete `decide`-closed theorems witnessing Euclid's formula on
  eight `(m, n)` pairs, plus an extra numeric witness at `(7, 4)`.
- A Euclidean `gcd` helper, used to witness primitivity of three
  small primitive triples.
- A handful of `n = 3` Fermat counterexamples: for several small
  `(a, b, c)` we compute `a³ + b³ ≠ c³` numerically.

What this module does **not** prove:

- No general Euclid parametrization theorem is proved here. We only
  witness the formula on the specific `(m, n)` pairs enumerated
  below. Kernel `decide` does not quantify over `m, n`.
- No claim is made that every primitive Pythagorean triple arises
  from Euclid's formula (that converse requires a proof, not
  witnesses). We only verify that specific outputs are primitive.
- The Fermat-exponent-3 witnesses rule out equality for a finite
  list of candidates. Fermat's theorem for `n = 3` as a universal
  statement is not proved here.

All proofs close by kernel `decide` or `rfl`. No `sorry`, no new
`axiom`, `Init`-only.
-/

namespace BuleyeanMath
namespace PythagoreanTriples

/-! ## Triple constructor and Pythagorean checker -/

/-- Euclid's triple generator. For `m > n ≥ 1`, `pythagTriple m n`
computes `(m² - n², 2 m n, m² + n²)`. The value at `m ≤ n` is
well-defined on `Nat` (using truncated subtraction) but is not a
Pythagorean triple in that regime. -/
def pythagTriple (m n : Nat) : Nat × Nat × Nat :=
  (m * m - n * n, 2 * m * n, m * m + n * n)

/-- `isPythag t` returns `true` iff the first two components squared
sum to the third component squared. -/
def isPythag : Nat × Nat × Nat → Bool
  | (a, b, c) => decide (a * a + b * b = c * c)

/-! ## Sanity checks on the triple constructor -/

/-- `pythagTriple 2 1` computes to `(3, 4, 5)`. -/
theorem pythagTriple_2_1 : pythagTriple 2 1 = (3, 4, 5) := by decide

/-- `pythagTriple 3 2` computes to `(5, 12, 13)`. -/
theorem pythagTriple_3_2 : pythagTriple 3 2 = (5, 12, 13) := by decide

/-- `pythagTriple 4 1` computes to `(15, 8, 17)`. -/
theorem pythagTriple_4_1 : pythagTriple 4 1 = (15, 8, 17) := by decide

/-- `pythagTriple 4 3` computes to `(7, 24, 25)`. -/
theorem pythagTriple_4_3 : pythagTriple 4 3 = (7, 24, 25) := by decide

/-- `pythagTriple 5 2` computes to `(21, 20, 29)`. -/
theorem pythagTriple_5_2 : pythagTriple 5 2 = (21, 20, 29) := by decide

/-- `pythagTriple 5 4` computes to `(9, 40, 41)`. -/
theorem pythagTriple_5_4 : pythagTriple 5 4 = (9, 40, 41) := by decide

/-- `pythagTriple 6 1` computes to `(35, 12, 37)`. -/
theorem pythagTriple_6_1 : pythagTriple 6 1 = (35, 12, 37) := by decide

/-- `pythagTriple 6 5` computes to `(11, 60, 61)`. -/
theorem pythagTriple_6_5 : pythagTriple 6 5 = (11, 60, 61) := by decide

/-- `pythagTriple 7 4` computes to `(33, 56, 65)`. -/
theorem pythagTriple_7_4 : pythagTriple 7 4 = (33, 56, 65) := by decide

/-! ## Euclid's formula on concrete `(m, n)` pairs

Each theorem witnesses `isPythag (pythagTriple m n) = true`, i.e.
`(m² - n²)² + (2 m n)² = (m² + n²)²` at the numerical level.
-/

/-- `(m, n) = (2, 1)` yields the triple `(3, 4, 5)`: `9 + 16 = 25`. -/
theorem euclid_2_1 : isPythag (pythagTriple 2 1) = true := by decide

/-- `(m, n) = (3, 2)` yields the triple `(5, 12, 13)`:
`25 + 144 = 169`. -/
theorem euclid_3_2 : isPythag (pythagTriple 3 2) = true := by decide

/-- `(m, n) = (4, 1)` yields the triple `(15, 8, 17)`:
`225 + 64 = 289`. -/
theorem euclid_4_1 : isPythag (pythagTriple 4 1) = true := by decide

/-- `(m, n) = (4, 3)` yields the triple `(7, 24, 25)`:
`49 + 576 = 625`. -/
theorem euclid_4_3 : isPythag (pythagTriple 4 3) = true := by decide

/-- `(m, n) = (5, 2)` yields the triple `(21, 20, 29)`:
`441 + 400 = 841`. -/
theorem euclid_5_2 : isPythag (pythagTriple 5 2) = true := by decide

/-- `(m, n) = (5, 4)` yields the triple `(9, 40, 41)`:
`81 + 1600 = 1681`. -/
theorem euclid_5_4 : isPythag (pythagTriple 5 4) = true := by decide

/-- `(m, n) = (6, 1)` yields the triple `(35, 12, 37)`:
`1225 + 144 = 1369`. -/
theorem euclid_6_1 : isPythag (pythagTriple 6 1) = true := by decide

/-- `(m, n) = (6, 5)` yields the triple `(11, 60, 61)`:
`121 + 3600 = 3721`. -/
theorem euclid_6_5 : isPythag (pythagTriple 6 5) = true := by decide

/-- Extra numeric instance at `(m, n) = (7, 4)`: `a = 33, b = 56,
c = 65`, and `33² + 56² = 1089 + 3136 = 4225 = 65²`. -/
theorem euclid_7_4 : isPythag (pythagTriple 7 4) = true := by decide

/-- Explicit algebraic identity on the `(7, 4)` numerics, closed by
`rfl` (pure reduction in `Nat`). -/
theorem pythag_identity_7_4 :
    (7 * 7 - 4 * 4) * (7 * 7 - 4 * 4)
        + (2 * 7 * 4) * (2 * 7 * 4)
      = (7 * 7 + 4 * 4) * (7 * 7 + 4 * 4) := by decide

/-! ## Euclidean `gcd` for primitivity witnesses

A primitive Pythagorean triple has pairwise coprime legs. We
provide a simple fuel-parameterized Euclidean algorithm and witness
`gcd(a, b) = 1` for several Euclid outputs whose `(m, n)` inputs are
coprime and of opposite parity.
-/

/-- Euclidean `gcd` with an explicit fuel argument, mirroring the
convention used in sibling modules. The fuel at the call site is
taken as `a + b + 1`, safely bounding the number of Euclidean
reduction steps. -/
def gcdFuel : Nat → Nat → Nat → Nat
  | 0,          a, _            => a
  | Nat.succ _, a, 0            => a
  | Nat.succ f, a, Nat.succ b   => gcdFuel f (Nat.succ b) (a % Nat.succ b)

/-- Euclidean `gcd` on `Nat`. -/
def gcdNat (a b : Nat) : Nat := gcdFuel (a + b + 1) a b

/-! ### Sanity checks on `gcdNat` -/

theorem gcd_6_4 : gcdNat 6 4 = 2 := by decide
theorem gcd_17_5 : gcdNat 17 5 = 1 := by decide
theorem gcd_21_14 : gcdNat 21 14 = 7 := by decide

/-! ### Primitivity witnesses

Each pair `(m, n)` below has `gcd(m, n) = 1` and opposite parity,
so the resulting triple is expected to be primitive. We verify one
pairwise gcd (`gcd(a, b) = 1`) per triple.
-/

/-- `(m, n) = (2, 1)` has `gcd = 1` and opposite parity. The output
`(3, 4, 5)` has `gcd(3, 4) = 1`. -/
theorem primitive_2_1_gcd_ab : gcdNat 3 4 = 1 := by decide

/-- `(m, n) = (3, 2)` has `gcd = 1` and opposite parity. The output
`(5, 12, 13)` has `gcd(5, 12) = 1`. -/
theorem primitive_3_2_gcd_ab : gcdNat 5 12 = 1 := by decide

/-- `(m, n) = (4, 1)` has `gcd = 1` and opposite parity. The output
`(15, 8, 17)` has `gcd(15, 8) = 1`. -/
theorem primitive_4_1_gcd_ab : gcdNat 15 8 = 1 := by decide

/-- `(m, n) = (4, 3)` has `gcd = 1` and opposite parity. The output
`(7, 24, 25)` has `gcd(7, 24) = 1`. -/
theorem primitive_4_3_gcd_ab : gcdNat 7 24 = 1 := by decide

/-- `(m, n) = (5, 2)` has `gcd = 1` and opposite parity. The output
`(21, 20, 29)` has `gcd(21, 20) = 1`. -/
theorem primitive_5_2_gcd_ab : gcdNat 21 20 = 1 := by decide

/-! ### Input pair coprimality (consistency check)

The inputs themselves are coprime, matching the primitivity
hypothesis of Euclid's classification. -/

theorem gcd_m_n_2_1 : gcdNat 2 1 = 1 := by decide
theorem gcd_m_n_3_2 : gcdNat 3 2 = 1 := by decide
theorem gcd_m_n_4_1 : gcdNat 4 1 = 1 := by decide
theorem gcd_m_n_4_3 : gcdNat 4 3 = 1 := by decide
theorem gcd_m_n_5_2 : gcdNat 5 2 = 1 := by decide

/-! ## Fermat exponent-3 negative witnesses

For the exponent `n = 3` case of Fermat's Last Theorem, there is no
triple of positive naturals `(a, b, c)` with `a³ + b³ = c³`. We
cannot prove the universal statement here, but we can witness
inequality on a handful of small candidates: reusing the
Pythagorean triples above, and a few other small triples.

Each witness is `a³ + b³ ≠ c³`, encoded as `decide` on a `Nat`
inequality so it closes by kernel reduction.
-/

/-- `a³` as a plain natural. -/
def cube (a : Nat) : Nat := a * a * a

theorem cube_3 : cube 3 = 27 := by decide
theorem cube_4 : cube 4 = 64 := by decide
theorem cube_5 : cube 5 = 125 := by decide

/-- `(3, 4, 5)` is Pythagorean but not a Fermat-3 solution:
`27 + 64 = 91 ≠ 125`. -/
theorem fermat3_not_3_4_5 : cube 3 + cube 4 ≠ cube 5 := by decide

/-- `(5, 12, 13)` is Pythagorean but not Fermat-3. -/
theorem fermat3_not_5_12_13 : cube 5 + cube 12 ≠ cube 13 := by decide

/-- `(7, 24, 25)` is Pythagorean but not Fermat-3. -/
theorem fermat3_not_7_24_25 : cube 7 + cube 24 ≠ cube 25 := by decide

/-- `(8, 15, 17)` (a Pythagorean triple) is not Fermat-3. -/
theorem fermat3_not_8_15_17 : cube 8 + cube 15 ≠ cube 17 := by decide

/-- `(1, 2, 3)` is not a Fermat-3 solution: `1 + 8 = 9 ≠ 27`. -/
theorem fermat3_not_1_2_3 : cube 1 + cube 2 ≠ cube 3 := by decide

/-- `(2, 3, 4)` is not a Fermat-3 solution: `8 + 27 = 35 ≠ 64`. -/
theorem fermat3_not_2_3_4 : cube 2 + cube 3 ≠ cube 4 := by decide

/-- `(6, 8, 10)` is not a Fermat-3 solution: `216 + 512 = 728 ≠ 1000`. -/
theorem fermat3_not_6_8_10 : cube 6 + cube 8 ≠ cube 10 := by decide

/-- `(9, 10, 12)` is not a Fermat-3 solution: `729 + 1000 = 1729 ≠ 1728`.
This is the "taxicab" near-miss `1729 = 1³ + 12³ = 9³ + 10³`, which
equals `12³ + 1³` but not `12³` alone. -/
theorem fermat3_not_9_10_12 : cube 9 + cube 10 ≠ cube 12 := by decide

end PythagoreanTriples
end BuleyeanMath
