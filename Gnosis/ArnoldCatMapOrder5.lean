import Init

/-!
# Arnold's Cat Map: `ord(A, 5) = 10`

This module witnesses the Formal Ledger entry "Cat Map Recurrence"
(`FORMAL_LEDGER.md` line 318): the Arnold cat-map matrix

    A = [ 2  1 ]
        [ 1  1 ]

has multiplicative order exactly `10` on `(ℤ/5)²`, i.e., the smallest
positive `k` with `A^k ≡ I (mod 5)` is `k = 10`.

## Encoding

Pairs `(x, y) ∈ (ℤ/n)²` are represented as `Nat × Nat` with every
coordinate kept reduced mod `n`. The cat map acts by

    CatMap n (x, y) = ((2 · x + y) % n, (x + y) % n).

Iterated application `catMapIter n k p` applies `CatMap n` to `p` a
total of `k` times. This is the natural coordinate-level witness of
matrix powering `A^k mod n`: `A^k (x, y) ≡ catMapIter n k (x, y)`.

## Proof strategy

* **Upper bound** `ord(A, 5) ∣ 10`: check that `A^10` fixes every
  one of the `25` points of `(ℤ/5)²`. This is closed by kernel
  `decide` on an `all`-quantifier over an explicit list.
* **Lower bound** `ord(A, 5) ∤ d` for every proper divisor `d` of
  `10`: it suffices to exhibit one non-fixed point for each of
  `d ∈ {1, 2, 5}`. We use `(1, 0)` in every case.
* **Order is exactly 10**: divisors of `10` are `{1, 2, 5, 10}`.
  The upper bound gives order `∣ 10`; the three lower-bound
  witnesses rule out `1, 2, 5`; so the order is `10`.

The `mod 2` and `mod 3` bonus checks use the same pattern. Note:
straightforward computation gives `ord(A, 3) = 4`, not `8` — the
cat-map order on `(ℤ/n)²` is the Pisano period `π(n)` of the
Fibonacci matrix `F = [[1,1],[1,0]]` divided by `2` when `π(n)`
is even (since `A = F²`), and `π(3) = 8 ⇒ ord(A, 3) = 4`. We
record the honest value here.

No `sorry`, no new `axiom`, `Init`-only, kernel `decide` only.
-/

namespace Gnosis
namespace ArnoldCatMapOrder5

/-! ## Coordinate-level cat map -/

/-- Arnold's cat map on the discrete torus `(ℤ/n)²`, viewed as
`Nat × Nat` with coordinates reduced mod `n`. -/
def CatMap (n : Nat) (p : Nat × Nat) : Nat × Nat :=
  ((2 * p.1 + p.2) % n, (p.1 + p.2) % n)

/-- `k`-fold application of `CatMap n`. -/
def catMapIter (n : Nat) : Nat → Nat × Nat → Nat × Nat
  | 0,     p => (p.1 % n, p.2 % n)
  | k + 1, p => CatMap n (catMapIter n k p)

/-! ## The 25 points of `(ℤ/5)²` -/

/-- Every pair `(x, y)` with `0 ≤ x, y < 5`. -/
def allPointsMod5 : List (Nat × Nat) :=
  [ (0,0), (0,1), (0,2), (0,3), (0,4)
  , (1,0), (1,1), (1,2), (1,3), (1,4)
  , (2,0), (2,1), (2,2), (2,3), (2,4)
  , (3,0), (3,1), (3,2), (3,3), (3,4)
  , (4,0), (4,1), (4,2), (4,3), (4,4)
  ]

/-- Sanity: the enumeration has `5 · 5 = 25` points. -/
theorem allPointsMod5_length : allPointsMod5.length = 25 := by decide

/-! ## Upper bound: `A^10` fixes every point of `(ℤ/5)²` -/

/-- **`A^10 ≡ I (mod 5)`**, witnessed pointwise.
For every `(x, y) ∈ (ℤ/5)²`, `catMapIter 5 10 (x, y) = (x, y)`.
Closed by kernel `decide` on `25` explicit pairs. -/
theorem catMap_pow_10_id_mod_5 :
    allPointsMod5.all (fun p => catMapIter 5 10 p == p) = true := by decide

/-! ## Lower bound: `(1, 0)` is not fixed by `A^1`, `A^2`, or `A^5` -/

/-- `A^1 (1, 0) = (2, 1) ≠ (1, 0)` mod `5`. Rules out order `1`. -/
theorem catMap_pow_1_not_id_mod_5 :
    catMapIter 5 1 (1, 0) ≠ (1, 0) := by decide

/-- `A^2 (1, 0) = (0, 3) ≠ (1, 0)` mod `5`. Rules out order `2`. -/
theorem catMap_pow_2_not_id_mod_5 :
    catMapIter 5 2 (1, 0) ≠ (1, 0) := by decide

/-- `A^5 (1, 0) = (4, 0) ≠ (1, 0)` mod `5`. Rules out order `5`. -/
theorem catMap_pow_5_not_id_mod_5 :
    catMapIter 5 5 (1, 0) ≠ (1, 0) := by decide

/-! ## Exact order

Divisors of `10` are `{1, 2, 5, 10}`. The upper bound witnesses
order-divides-`10`; the three lower-bound witnesses rule out the
proper divisors `1, 2, 5`. Hence `ord(A, 5) = 10`. -/

/-- **`ord(A, 5) = 10`** packaged as the four decidable checks.
Upper bound: `A^10` fixes all `25` points of `(ℤ/5)²`.
Lower bounds: `A^1`, `A^2`, `A^5` each move the point `(1, 0)`. -/
theorem ord_A_mod_5_eq_10 :
    allPointsMod5.all (fun p => catMapIter 5 10 p == p) = true ∧
    catMapIter 5 1 (1, 0) ≠ (1, 0) ∧
    catMapIter 5 2 (1, 0) ≠ (1, 0) ∧
    catMapIter 5 5 (1, 0) ≠ (1, 0) :=
  ⟨catMap_pow_10_id_mod_5,
   catMap_pow_1_not_id_mod_5,
   catMap_pow_2_not_id_mod_5,
   catMap_pow_5_not_id_mod_5⟩

/-! ## Bonus: `ord(A, 2) = 3`

Divisors of `3` are `{1, 3}`. Rule out `1` by exhibiting a non-fixed
point; then `A^3 ≡ I (mod 2)` on all `4` points closes the upper
bound. -/

/-- Every pair `(x, y)` with `0 ≤ x, y < 2`. -/
def allPointsMod2 : List (Nat × Nat) :=
  [ (0,0), (0,1), (1,0), (1,1) ]

theorem allPointsMod2_length : allPointsMod2.length = 4 := by decide

/-- `A^3 ≡ I (mod 2)` pointwise on `(ℤ/2)²`. -/
theorem catMap_pow_3_id_mod_2 :
    allPointsMod2.all (fun p => catMapIter 2 3 p == p) = true := by decide

/-- `A^1 (1, 0) = (0, 1) ≠ (1, 0)` mod `2`. Rules out order `1`. -/
theorem catMap_pow_1_not_id_mod_2 :
    catMapIter 2 1 (1, 0) ≠ (1, 0) := by decide

/-- **`ord(A, 2) = 3`** as the conjunction of the upper and lower
bounds on the only proper divisor `1`. -/
theorem ord_A_mod_2_eq_3 :
    allPointsMod2.all (fun p => catMapIter 2 3 p == p) = true ∧
    catMapIter 2 1 (1, 0) ≠ (1, 0) :=
  ⟨catMap_pow_3_id_mod_2, catMap_pow_1_not_id_mod_2⟩

/-! ## Bonus: `ord(A, 3) = 4`

The ledger's companion claim `ord(A, 3) = 8` over-counts: `A = F²`
where `F = [[1,1],[1,0]]` is the Fibonacci matrix with Pisano
period `π(3) = 8`, so `ord(A, 3) = π(3) / 2 = 4`. We record the
honest computed value. -/

/-- Every pair `(x, y)` with `0 ≤ x, y < 3`. -/
def allPointsMod3 : List (Nat × Nat) :=
  [ (0,0), (0,1), (0,2)
  , (1,0), (1,1), (1,2)
  , (2,0), (2,1), (2,2) ]

theorem allPointsMod3_length : allPointsMod3.length = 9 := by decide

/-- `A^4 ≡ I (mod 3)` pointwise on `(ℤ/3)²`. -/
theorem catMap_pow_4_id_mod_3 :
    allPointsMod3.all (fun p => catMapIter 3 4 p == p) = true := by decide

/-- `A^1 (1, 0) = (2, 1) ≠ (1, 0)` mod `3`. Rules out order `1`. -/
theorem catMap_pow_1_not_id_mod_3 :
    catMapIter 3 1 (1, 0) ≠ (1, 0) := by decide

/-- `A^2 (1, 0) = (2, 0) ≠ (1, 0)` mod `3`. Rules out order `2`. -/
theorem catMap_pow_2_not_id_mod_3 :
    catMapIter 3 2 (1, 0) ≠ (1, 0) := by decide

/-- **`ord(A, 3) = 4`** as the conjunction of the upper bound on
`A^4` and lower bounds on proper divisors `1, 2`. -/
theorem ord_A_mod_3_eq_4 :
    allPointsMod3.all (fun p => catMapIter 3 4 p == p) = true ∧
    catMapIter 3 1 (1, 0) ≠ (1, 0) ∧
    catMapIter 3 2 (1, 0) ≠ (1, 0) :=
  ⟨catMap_pow_4_id_mod_3,
   catMap_pow_1_not_id_mod_3,
   catMap_pow_2_not_id_mod_3⟩

/-! ## Trace check

The characteristic polynomial of `A` is `x² − 3·x + 1`, so the
trace sequence `t_k = tr(A^k)` satisfies `t_{k+1} = 3·t_k − t_{k-1}`
with `t_0 = 2, t_1 = 3`. This is a Lucas-type recurrence. We
record the first eight traces directly so downstream modules can
cite the sequence without recomputing. -/

/-- Trace of `A^k` as a `Nat`. Defined by the Lucas-type recurrence
`t_{k+1} = 3 · t_k − t_{k-1}`. Kept in `Nat` via `(3 * tk) - tk₁`;
monotonic for the small indices used here. -/
def traceCatPow : Nat → Nat
  | 0     => 2
  | 1     => 3
  | k + 2 => 3 * traceCatPow (k + 1) - traceCatPow k

/-- First eight trace values:
`2, 3, 7, 18, 47, 123, 322, 843`. These match `tr(A^k)` as
computed from `A^k` directly (sanity check for the Lucas tie-in
described in the ledger). -/
theorem traceCatPow_table :
    traceCatPow 0 = 2   ∧ traceCatPow 1 = 3   ∧
    traceCatPow 2 = 7   ∧ traceCatPow 3 = 18  ∧
    traceCatPow 4 = 47  ∧ traceCatPow 5 = 123 ∧
    traceCatPow 6 = 322 ∧ traceCatPow 7 = 843 := by decide

end ArnoldCatMapOrder5
end Gnosis
