import Init

/-!
# Stirling numbers of the second kind and Bell numbers: small-instance table

This module witnesses the usual small-`n` facts about the Stirling
numbers of the second kind `S(n, k)` and the Bell numbers `B(n)`.

* `stirling n k` computes `S(n, k)` by the two-argument recurrence
  `S(n+1, k+1) = (k+1) · S(n, k+1) + S(n, k)`,
  with boundary `S(0, 0) = 1`, `S(0, k+1) = 0`, `S(n+1, 0) = 0`.
* `bell n` sums a row of the Stirling table:
  `B(n) = Σ_{k=0}^{n} S(n, k)`.
* `binom n k` is a Pascal-rule binomial coefficient, used only to
  cross-check Bell's binomial recurrence
  `B(n+1) = Σ_{k=0}^{n} C(n, k) · B(k)` at a single `n`.

The Stirling table is closed for `n ∈ {0, …, 6}` and all `k ∈ {0, …, n}`.
The Bell sequence `B(0), …, B(7) = 1, 1, 2, 5, 15, 52, 203, 877` is
witnessed by `decide` via the Stirling-row sum.

## Caveats

* This is not a general proof of `S(n+1, k+1) = (k+1) · S(n, k+1) +
  S(n, k)` as a theorem over all `n, k`; the equality is witnessed at
  a single representative point (`n = 4, k = 2`, giving `S(5, 3) = 25`).
* Likewise for the Bell binomial recurrence
  `B(n+1) = Σ_{k=0}^{n} C(n, k) · B(k)`: checked at a single `n` (`n = 4`,
  giving `B(5) = 52`), not as a general theorem.
* Nothing here connects `B(n)` to its exponential generating function
  `e^{e^x - 1}`, and Touchard's congruence `B(n+p) ≡ B(n) + B(n+1) (mod p)`
  is not addressed.
* The counting interpretation ("S(n, k) counts partitions of an
  n-set into k non-empty blocks") is not formalised as a bijection
  with a `Finset` of partitions — only the recurrence's arithmetic
  output is checked.

No `sorry`, no new `axiom`, `Init`-only, kernel `decide` only.
-/

namespace Gnosis
namespace StirlingBellSmall

/-! ## Stirling numbers of the second kind -/

/-- `stirling n k` computes `S(n, k)` by the standard two-argument
recurrence. Structurally recursive on the first argument:

* `stirling 0 0        = 1`
* `stirling 0 (k+1)    = 0`
* `stirling (n+1) 0    = 0`
* `stirling (n+1) (k+1) = (k+1) · stirling n (k+1) + stirling n k`.

The recurrence witnesses "put element `n+1` into one of the `k+1`
existing blocks" (the `(k+1) · stirling n (k+1)` term) or "open a new
singleton block" (the `stirling n k` term). -/
def stirling : Nat → Nat → Nat
  | 0,     0     => 1
  | 0,     _ + 1 => 0
  | _ + 1, 0     => 0
  | n + 1, k + 1 => (k + 1) * stirling n (k + 1) + stirling n k

/-! ## Bell numbers via Stirling-row sum -/

/-- Sum `Σ_{k=0}^{m} stirling n k`, built by structural recursion on
`m`. Used only with `m = n` to read off `bell n`. -/
def stirlingRowSumUpTo (n : Nat) : Nat → Nat
  | 0     => stirling n 0
  | m + 1 => stirlingRowSumUpTo n m + stirling n (m + 1)

/-- `bell n = Σ_{k=0}^{n} S(n, k)`, the total number of set
partitions of an `n`-element set. -/
def bell (n : Nat) : Nat :=
  stirlingRowSumUpTo n n

/-! ## Binomial coefficient (for Bell's binomial recurrence) -/

/-- Pascal-rule binomial coefficient `C(n, k)` on `Nat`:
`binom n 0 = 1`, `binom 0 (k+1) = 0`,
`binom (n+1) (k+1) = binom n k + binom n (k+1)`. -/
def binom : Nat → Nat → Nat
  | _,     0     => 1
  | 0,     _ + 1 => 0
  | n + 1, k + 1 => binom n k + binom n (k + 1)

/-! ## Stirling table for `n ∈ {0, …, 6}` -/

/-- Row `n = 0`: only `S(0, 0) = 1`. -/
theorem stirling_row_0 : stirling 0 0 = 1 := by decide

/-- Row `n = 1`: `S(1, 0) = 0`, `S(1, 1) = 1`. -/
theorem stirling_row_1 :
    stirling 1 0 = 0 ∧ stirling 1 1 = 1 := by decide

/-- Row `n = 2`: `0, 1, 1`. -/
theorem stirling_row_2 :
    stirling 2 0 = 0 ∧ stirling 2 1 = 1 ∧ stirling 2 2 = 1 := by decide

/-- Row `n = 3`: `0, 1, 3, 1`. -/
theorem stirling_row_3 :
    stirling 3 0 = 0 ∧ stirling 3 1 = 1 ∧
    stirling 3 2 = 3 ∧ stirling 3 3 = 1 := by decide

/-- Row `n = 4`: `0, 1, 7, 6, 1`. -/
theorem stirling_row_4 :
    stirling 4 0 = 0 ∧ stirling 4 1 = 1 ∧
    stirling 4 2 = 7 ∧ stirling 4 3 = 6 ∧
    stirling 4 4 = 1 := by decide

/-- Row `n = 5`: `0, 1, 15, 25, 10, 1`. -/
theorem stirling_row_5 :
    stirling 5 0 = 0  ∧ stirling 5 1 = 1  ∧
    stirling 5 2 = 15 ∧ stirling 5 3 = 25 ∧
    stirling 5 4 = 10 ∧ stirling 5 5 = 1 := by decide

/-- Row `n = 6`: `0, 1, 31, 90, 65, 15, 1`. -/
theorem stirling_row_6 :
    stirling 6 0 = 0  ∧ stirling 6 1 = 1  ∧
    stirling 6 2 = 31 ∧ stirling 6 3 = 90 ∧
    stirling 6 4 = 65 ∧ stirling 6 5 = 15 ∧
    stirling 6 6 = 1 := by decide

/-! ## Bell sequence `B(0), …, B(7)`

`1, 1, 2, 5, 15, 52, 203, 877`. Computed as the Stirling-row sum. -/

/-- First eight Bell numbers by row-sum over the Stirling table. -/
theorem bell_table :
    bell 0 = 1  ∧ bell 1 = 1   ∧
    bell 2 = 2  ∧ bell 3 = 5   ∧
    bell 4 = 15 ∧ bell 5 = 52  ∧
    bell 6 = 203 ∧ bell 7 = 877 := by decide

/-! ## Recurrence cross-check at a single Stirling point

`S(5, 3) = 3 · S(4, 3) + S(4, 2) = 3 · 6 + 7 = 25`. Witnessed in two
stages: the recurrence holds on these values, and the arithmetic sums
to `25`. Not a general theorem over all `n, k`. -/

/-- The Stirling recurrence holds at `n = 4, k = 2`. -/
theorem stirling_recurrence_5_3 :
    stirling 5 3 = 3 * stirling 4 3 + stirling 4 2 := by decide

/-- The right-hand side of the recurrence at `(5, 3)` evaluates to `25`. -/
theorem stirling_recurrence_5_3_eq_25 :
    3 * stirling 4 3 + stirling 4 2 = 25 := by decide

/-! ## Bell equals sum of Stirling row, spelled out at `n = 4`

`B(4) = S(4,0) + S(4,1) + S(4,2) + S(4,3) + S(4,4)
      = 0 + 1 + 7 + 6 + 1 = 15`. -/

/-- `bell 4` equals the explicit sum of row `n = 4` of the Stirling
table. -/
theorem bell_4_eq_stirling_row_4_sum :
    bell 4 =
      stirling 4 0 + stirling 4 1 + stirling 4 2
      + stirling 4 3 + stirling 4 4 := by decide

/-- That explicit sum evaluates to `15`. -/
theorem stirling_row_4_sum_eq_15 :
    stirling 4 0 + stirling 4 1 + stirling 4 2
    + stirling 4 3 + stirling 4 4 = 15 := by decide

/-! ## Bell's binomial recurrence at a single point

`B(5) = Σ_{k=0}^{4} C(4, k) · B(k)
      = 1·1 + 4·1 + 6·2 + 4·5 + 1·15
      = 1 + 4 + 12 + 20 + 15
      = 52`.

Not a general theorem — witnessed only at `n + 1 = 5`. -/

/-- Row `n = 4` of Pascal's triangle: `1, 4, 6, 4, 1`. -/
theorem binom_row_4 :
    binom 4 0 = 1 ∧ binom 4 1 = 4 ∧ binom 4 2 = 6 ∧
    binom 4 3 = 4 ∧ binom 4 4 = 1 := by decide

/-- `B(5)` equals the binomial convolution `Σ_{k=0}^{4} C(4, k) · B(k)`. -/
theorem bell_5_binomial_recurrence :
    bell 5 =
      binom 4 0 * bell 0
      + binom 4 1 * bell 1
      + binom 4 2 * bell 2
      + binom 4 3 * bell 3
      + binom 4 4 * bell 4 := by decide

/-- That binomial convolution evaluates to `52`. -/
theorem bell_5_binomial_recurrence_eq_52 :
    binom 4 0 * bell 0
    + binom 4 1 * bell 1
    + binom 4 2 * bell 2
    + binom 4 3 * bell 3
    + binom 4 4 * bell 4 = 52 := by decide

end StirlingBellSmall
end Gnosis
