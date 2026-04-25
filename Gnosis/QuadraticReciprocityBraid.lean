import Init

/-!
# Quadratic Reciprocity as a k=2 Braid

The reciprocity sign `(p/q)·(q/p) = (−1)^((p−1)/2 · (q−1)/2)` is a
`k=2` braid on the product parity of `(p−1)/2` and `(q−1)/2`.

For odd primes `p, q`:

- `p ≡ 1 (mod 4)`: `(p−1)/2` is even.
- `p ≡ 3 (mod 4)`: `(p−1)/2` is odd.

The sign is `−1` if and only if **both** `p` and `q` are `≡ 3 (mod
4)`. Otherwise `+1`. This is a non-trivial `k=2` phase filter — the
"minus phase" is the rare joint `(3, 3) mod 4` case.

## Why this is a braid, not just a sign

The cycle is the parity `(p mod 4, q mod 4)` viewed as a `ℤ/2 × ℤ/2`
product (itself a tensor braid from `BraidTensorProduct`). But the
reciprocity identity collapses the 2×2 = 4 cells into the sign:

    (1,1) → +1, (1,3) → +1, (3,1) → +1, (3,3) → −1

Three plus-phase cells, one minus-phase cell. The clinamen that
advances the phase is not `+1 mod 2` — it is a specific identification
of the four cases into the sign `(−1)^odd_count`.

The unbraidability: knowing only `p mod 4` doesn't tell you the sign;
you need both `p mod 4` AND `q mod 4`. The two primes' phases are
coupled, and the coupling is the reciprocity law itself.

## What this module witnesses

- The parity function and sign computation.
- Concrete instances for pairs `(p, q)` spanning all four cases:
  - Both `≡ 1 mod 4`: `(5, 13), (13, 17)`
  - Mixed `(1, 3), (3, 1)`: `(5, 7), (13, 3)`
  - Both `≡ 3 mod 4`: `(3, 7), (7, 11)`
- The `k=2` braid structure on the parity product.

`import Init` only. Zero `sorry`, zero new `axiom`.
-/

namespace Gnosis
namespace QuadraticReciprocityBraid

/-! ## The sign function -/

/-- `(p − 1) / 2` parity: 0 if `p ≡ 1 mod 4`, 1 if `p ≡ 3 mod 4`. -/
def halfParity (p : Nat) : Nat := ((p - 1) / 2) % 2

/-- The reciprocity sign: `(−1)^(halfParity p · halfParity q)`. -/
def reciprocitySign (p q : Nat) : Int :=
  if (halfParity p * halfParity q) % 2 = 0 then 1 else -1

/-! ## Half-parity values

`halfParity` on small primes:
- 3: (3-1)/2 = 1, mod 2 = 1
- 5: (5-1)/2 = 2, mod 2 = 0
- 7: (7-1)/2 = 3, mod 2 = 1
- 11: (11-1)/2 = 5, mod 2 = 1
- 13: (13-1)/2 = 6, mod 2 = 0
- 17: (17-1)/2 = 8, mod 2 = 0
- 19: (19-1)/2 = 9, mod 2 = 1
- 23: (23-1)/2 = 11, mod 2 = 1
-/

theorem halfParity_3 : halfParity 3 = 1 := by decide
theorem halfParity_5 : halfParity 5 = 0 := by decide
theorem halfParity_7 : halfParity 7 = 1 := by decide
theorem halfParity_11 : halfParity 11 = 1 := by decide
theorem halfParity_13 : halfParity 13 = 0 := by decide
theorem halfParity_17 : halfParity 17 = 0 := by decide

/-! ## Sign witnesses across all four cases

Case 1: both ≡ 1 mod 4 → +1
Case 2: `(1, 3)` mix → +1
Case 3: `(3, 1)` mix → +1
Case 4: both ≡ 3 mod 4 → −1 (the only minus phase) -/

/-! ### Case 1: both ≡ 1 mod 4, sign = +1 -/

theorem sign_5_13 : reciprocitySign 5 13 = 1 := by decide
theorem sign_13_17 : reciprocitySign 13 17 = 1 := by decide
theorem sign_5_17 : reciprocitySign 5 17 = 1 := by decide

/-! ### Case 2: `p ≡ 1, q ≡ 3` mix, sign = +1 -/

theorem sign_5_7 : reciprocitySign 5 7 = 1 := by decide
theorem sign_5_11 : reciprocitySign 5 11 = 1 := by decide
theorem sign_13_3 : reciprocitySign 13 3 = 1 := by decide

/-! ### Case 3: `p ≡ 3, q ≡ 1` mix, sign = +1 (symmetric) -/

theorem sign_3_13 : reciprocitySign 3 13 = 1 := by decide
theorem sign_7_5 : reciprocitySign 7 5 = 1 := by decide
theorem sign_11_17 : reciprocitySign 11 17 = 1 := by decide

/-! ### Case 4: both ≡ 3 mod 4, sign = −1 -/

theorem sign_3_7 : reciprocitySign 3 7 = -1 := by decide
theorem sign_3_11 : reciprocitySign 3 11 = -1 := by decide
theorem sign_7_11 : reciprocitySign 7 11 = -1 := by decide
theorem sign_11_19 : reciprocitySign 11 19 = -1 := by decide

/-! ## The k=2 structure

Sign takes only two values: `+1` and `−1`. Advancing either prime
through all residues mod 4 traces a `k=2` cycle on the sign — but
the cycle's generator is NOT `+1 mod 4`; it is the coupled parity
flip that depends on both primes simultaneously. -/

/-- Three of four cases are "plus"; one is "minus." -/
theorem three_of_four_are_plus :
    reciprocitySign 5 13 = 1  -- (1, 1)
    ∧ reciprocitySign 5 7 = 1   -- (1, 3)
    ∧ reciprocitySign 7 5 = 1   -- (3, 1)
    ∧ reciprocitySign 3 7 = -1 := by decide  -- (3, 3)

/-! ## Unbraidability — knowing one prime isn't enough

Given only `p = 7` (with `halfParity = 1`), we cannot determine the
sign. For `q = 5` sign is +1; for `q = 11` sign is −1. The braid's
truth lives in the coupling. -/

theorem p_7_underdetermined :
    reciprocitySign 7 5 = 1
    ∧ reciprocitySign 7 11 = -1
    ∧ (1 : Int) ≠ -1 := by decide

/-! ## The 4-cell parity grid -/

/-- Compute the sign-grid index: the pair `(halfParity p, halfParity
q)` encoded into `{0, 1, 2, 3}`. -/
def gridCell (p q : Nat) : Nat :=
  2 * halfParity p + halfParity q

theorem grid_5_13 : gridCell 5 13 = 0 := by decide    -- (0, 0)
theorem grid_5_7 : gridCell 5 7 = 1 := by decide      -- (0, 1)
theorem grid_3_13 : gridCell 3 13 = 2 := by decide    -- (1, 0)
theorem grid_3_7 : gridCell 3 7 = 3 := by decide      -- (1, 1)

/-- Cells `{0, 1, 2}` are plus-phase; cell `3` is the minus-phase. -/
theorem plus_cells_0_1_2 :
    reciprocitySign 5 13 = 1
    ∧ reciprocitySign 5 7 = 1
    ∧ reciprocitySign 3 13 = 1 := by decide

theorem minus_cell_3 : reciprocitySign 3 7 = -1 := by decide

/-! ## Master witness -/

theorem quadratic_reciprocity_braid_master :
    -- Half-parity correctness
    halfParity 3 = 1 ∧ halfParity 5 = 0
    ∧ halfParity 7 = 1 ∧ halfParity 11 = 1
    ∧ halfParity 13 = 0 ∧ halfParity 17 = 0
    -- Four-cell grid, three-plus one-minus
    ∧ reciprocitySign 5 13 = 1   -- (1, 1)
    ∧ reciprocitySign 5 7 = 1    -- (1, 3)
    ∧ reciprocitySign 7 5 = 1    -- (3, 1)
    ∧ reciprocitySign 3 7 = -1   -- (3, 3)
    -- Unbraidability
    ∧ reciprocitySign 7 5 = 1
    ∧ reciprocitySign 7 11 = -1
    ∧ (1 : Int) ≠ -1 := by
  decide

/-! ## Reading

Quadratic reciprocity's sign is the simplest possible `k=2` braid
with **non-trivial coupling**. Unlike Cassini's parity (determined
by `n` alone), the reciprocity sign requires BOTH primes. It's a
function on `ℤ/4 × ℤ/4` that collapses through `ℤ/2 × ℤ/2` to
`ℤ/2` (the sign).

This makes QR a **coupled** `k=2` braid, in the tensor-product
sense from `BraidTensorProduct`. The coupling is the reciprocity
law itself. Classical math sees QR as a single sign formula; the
braid view sees it as the phase projection of a tensor product of
two `k=2` parity braids through a specific product-to-sum map.

Unbraidability is automatic: you can't "ignore" one prime and keep
the sign intact. The law couples them.
-/

end QuadraticReciprocityBraid
end Gnosis
