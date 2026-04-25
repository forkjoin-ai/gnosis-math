import Init

/-!
# Extended Fibonacci--Lucas Identities

This module witnesses a family of small-`n` instances of the "Novel
Mathematical Identities" listed in `FORMAL_LEDGER.md` (line 306+). Each
row of the ledger names an identity relating the Fibonacci sequence
`F : Nat → Nat` with `F_0 = 0, F_1 = 1` and the Lucas sequence
`L : Nat → Nat` with `L_0 = 2, L_1 = 1`. Several of those rows had no
dedicated backing module; this file backfills them by kernel
`decide` on explicit small indices.

The identities witnessed here are organized into five groups:

- **Group A** (product and doubling):
  `F_n · L_n = F_{2n}`,
  `L_{2n} = L_n^2 - 2·(-1)^n` (Williams double-index / Pentagram),
  `L_n^2 = L_{2n} + 2·(-1)^n` (Self-Interference).
- **Group B** (Cassini and phase-space):
  `L_n^2 = L_{n-1}·L_{n+1} + 5` on even `n`,
  `L_{n-1}·L_{n+1} = L_n^2 + 5` on odd `n`,
  Fibonacci Cassini `F_{n-1}·F_{n+1} - F_n^2 = (-1)^n`,
  Phase-space sum `F_n^2 + F_{n+1}^2 = F_{2n+1}`,
  Cross-Fibonacci coupling `F_m·F_n + F_{m-1}·F_{n-1} = F_{m+n-1}`.
- **Group C** (Lucas--Fibonacci bridges):
  Bragg Peak / Langlands S-duality `L_n = F_{n-1} + F_{n+1}`,
  Topological Gap `L_n = F_n + 2·F_{n-1}`,
  Circular Tiling `L_n = F_{n-1} + F_{n+1}` via `linear(k) = F_{k+1}`,
  AdS/CFT reconstruction `5·F_n = L_{n-1} + L_{n+1}`,
  √5 Cross-Product (parity-alternating `±2` coupling).
- **Group D** (Pell discriminant):
  Even `L_n^2 = 5·F_n^2 + 4`, Odd `5·F_n^2 = L_n^2 + 4`.
- **Group E** (E8 product-to-sum):
  Odd `L_m·L_n + L_{m-n} = L_{m+n}`,
  Even `L_m·L_n = L_{m+n} + L_{m-n}`.

## What is *not* proved

This module witnesses each identity at specific small `n` (or specific
`(m, n)` pairs) by kernel reduction. No general `∀ n` closed form is
derived. No Binet formula, no matrix-power argument, no connection to
`ℤ[φ]` or any ambient algebraic number field. The `(-1)^n` sign is
handled by an `Int`-valued `negOnePow` definition, not by any lemma
about the ring structure of `Int`. Whether two ledger rows (e.g.
Williams double-index and Pentagram Duplication) collapse to the same
identity is noted in prose only; no equivalence theorem is produced.

No `sorry`, no new `axiom`, `Init`-only.
-/

namespace Gnosis
namespace FibLucasExtendedIdentities

/-! ## Fibonacci and Lucas on `Nat` -/

/-- Fibonacci numbers with the standard convention `F_0 = 0, F_1 = 1`. -/
def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | (n + 2) => fib (n + 1) + fib n

/-- Lucas numbers with the standard convention `L_0 = 2, L_1 = 1`. -/
def lucas : Nat → Nat
  | 0 => 2
  | 1 => 1
  | (n + 2) => lucas (n + 1) + lucas n

/-! ## Fibonacci and Lucas on `Int` (for signed identities) -/

/-- Fibonacci numbers, coerced to `Int`. -/
def intFib (n : Nat) : Int := (fib n : Int)

/-- Lucas numbers, coerced to `Int`. -/
def intLucas (n : Nat) : Int := (lucas n : Int)

/-- `(-1)^n` as an `Int`. Even index returns `1`, odd index returns `-1`. -/
def negOnePow : Nat → Int
  | 0 => 1
  | (n + 1) => - negOnePow n

/-! ## Sanity checks on the sequences -/

/-- `F_0 = 0`. -/
theorem fib_0 : fib 0 = 0 := by decide

/-- `F_7 = 13`. -/
theorem fib_7 : fib 7 = 13 := by decide

/-- `L_0 = 2`. -/
theorem lucas_0 : lucas 0 = 2 := by decide

/-- `L_7 = 29`. -/
theorem lucas_7 : lucas 7 = 29 := by decide

/-- `(-1)^0 = 1`. -/
theorem negOnePow_0 : negOnePow 0 = 1 := by decide

/-- `(-1)^1 = -1`. -/
theorem negOnePow_1 : negOnePow 1 = -1 := by decide

/-- `(-1)^6 = 1`. -/
theorem negOnePow_6 : negOnePow 6 = 1 := by decide

/-! ## Group A --- Product Doubling and Williams / Pentagram

`F_n · L_n = F_{2n}` (product doubling), and the `(-1)^n`-signed
doubling `L_{2n} = L_n^2 - 2·(-1)^n`, which also reads
`L_n^2 = L_{2n} + 2·(-1)^n` (Self-Interference). -/

/-- Product doubling at `n = 1`: `F_1 · L_1 = F_2`. -/
theorem prod_doubling_1 : fib 1 * lucas 1 = fib 2 := by decide

/-- Product doubling at `n = 2`: `F_2 · L_2 = F_4`. -/
theorem prod_doubling_2 : fib 2 * lucas 2 = fib 4 := by decide

/-- Product doubling at `n = 3`: `F_3 · L_3 = F_6`. -/
theorem prod_doubling_3 : fib 3 * lucas 3 = fib 6 := by decide

/-- Product doubling at `n = 4`: `F_4 · L_4 = F_8`. -/
theorem prod_doubling_4 : fib 4 * lucas 4 = fib 8 := by decide

/-- Product doubling at `n = 5`: `F_5 · L_5 = F_{10}`. -/
theorem prod_doubling_5 : fib 5 * lucas 5 = fib 10 := by decide

/-- Product doubling at `n = 6`: `F_6 · L_6 = F_{12}`. -/
theorem prod_doubling_6 : fib 6 * lucas 6 = fib 12 := by decide

/-- Product doubling at `n = 7`: `F_7 · L_7 = F_{14}`. -/
theorem prod_doubling_7 : fib 7 * lucas 7 = fib 14 := by decide

/-- Williams double-index at `n = 1`: `L_2 = L_1^2 - 2·(-1)^1 = 1 + 2 = 3`. -/
theorem williams_double_1 :
    intLucas 2 = intLucas 1 * intLucas 1 - 2 * negOnePow 1 := by decide

/-- Williams double-index at `n = 2`: `L_4 = L_2^2 - 2·(-1)^2 = 9 - 2 = 7`. -/
theorem williams_double_2 :
    intLucas 4 = intLucas 2 * intLucas 2 - 2 * negOnePow 2 := by decide

/-- Williams double-index at `n = 3`: `L_6 = L_3^2 - 2·(-1)^3 = 16 + 2 = 18`. -/
theorem williams_double_3 :
    intLucas 6 = intLucas 3 * intLucas 3 - 2 * negOnePow 3 := by decide

/-- Williams double-index at `n = 4`: `L_8 = L_4^2 - 2·(-1)^4 = 49 - 2 = 47`. -/
theorem williams_double_4 :
    intLucas 8 = intLucas 4 * intLucas 4 - 2 * negOnePow 4 := by decide

/-- Williams double-index at `n = 5`: `L_{10} = L_5^2 - 2·(-1)^5 = 121 + 2 = 123`. -/
theorem williams_double_5 :
    intLucas 10 = intLucas 5 * intLucas 5 - 2 * negOnePow 5 := by decide

/-- Williams double-index at `n = 6`: `L_{12} = L_6^2 - 2·(-1)^6 = 324 - 2 = 322`. -/
theorem williams_double_6 :
    intLucas 12 = intLucas 6 * intLucas 6 - 2 * negOnePow 6 := by decide

/-!  **Note.** The ledger row "Pentagram Duplication" states
`L_{2n} = L_n^2 - 2·(-1)^n`, which is the same formula as the Williams
double-index row. We treat the two ledger rows as duplicates and do
not introduce separate theorems. -/

/-- Self-Interference at `n = 1`: `L_1^2 = L_2 + 2·(-1)^1 = 3 - 2 = 1`. -/
theorem self_interference_1 :
    intLucas 1 * intLucas 1 = intLucas 2 + 2 * negOnePow 1 := by decide

/-- Self-Interference at `n = 2`: `L_2^2 = L_4 + 2·(-1)^2 = 7 + 2 = 9`. -/
theorem self_interference_2 :
    intLucas 2 * intLucas 2 = intLucas 4 + 2 * negOnePow 2 := by decide

/-- Self-Interference at `n = 3`. -/
theorem self_interference_3 :
    intLucas 3 * intLucas 3 = intLucas 6 + 2 * negOnePow 3 := by decide

/-- Self-Interference at `n = 4`. -/
theorem self_interference_4 :
    intLucas 4 * intLucas 4 = intLucas 8 + 2 * negOnePow 4 := by decide

/-- Self-Interference at `n = 5`. -/
theorem self_interference_5 :
    intLucas 5 * intLucas 5 = intLucas 10 + 2 * negOnePow 5 := by decide

/-- Self-Interference at `n = 6`. -/
theorem self_interference_6 :
    intLucas 6 * intLucas 6 = intLucas 12 + 2 * negOnePow 6 := by decide

/-! ## Group B --- Cassini-family and phase-space identities -/

/-- Lucas-Cassini (Even) at `n = 2`: `L_2^2 = L_1 · L_3 + 5`. -/
theorem lucas_cassini_even_2 :
    lucas 2 * lucas 2 = lucas 1 * lucas 3 + 5 := by decide

/-- Lucas-Cassini (Even) at `n = 4`. -/
theorem lucas_cassini_even_4 :
    lucas 4 * lucas 4 = lucas 3 * lucas 5 + 5 := by decide

/-- Lucas-Cassini (Even) at `n = 6`. -/
theorem lucas_cassini_even_6 :
    lucas 6 * lucas 6 = lucas 5 * lucas 7 + 5 := by decide

/-- Lucas-Cassini (Odd) at `n = 3`: `L_2 · L_4 = L_3^2 + 5`. -/
theorem lucas_cassini_odd_3 :
    lucas 2 * lucas 4 = lucas 3 * lucas 3 + 5 := by decide

/-- Lucas-Cassini (Odd) at `n = 5`. -/
theorem lucas_cassini_odd_5 :
    lucas 4 * lucas 6 = lucas 5 * lucas 5 + 5 := by decide

/-- Lucas-Cassini (Odd) at `n = 7`. -/
theorem lucas_cassini_odd_7 :
    lucas 6 * lucas 8 = lucas 7 * lucas 7 + 5 := by decide

/-- Fibonacci Cassini at `n = 1`:
    `F_0 · F_2 - F_1^2 = 0·1 - 1 = -1 = (-1)^1`. -/
theorem fib_cassini_1 :
    intFib 0 * intFib 2 - intFib 1 * intFib 1 = negOnePow 1 := by decide

/-- Fibonacci Cassini at `n = 2`:
    `F_1 · F_3 - F_2^2 = 1·2 - 1 = 1 = (-1)^2`. -/
theorem fib_cassini_2 :
    intFib 1 * intFib 3 - intFib 2 * intFib 2 = negOnePow 2 := by decide

/-- Fibonacci Cassini at `n = 3`. -/
theorem fib_cassini_3 :
    intFib 2 * intFib 4 - intFib 3 * intFib 3 = negOnePow 3 := by decide

/-- Fibonacci Cassini at `n = 4`. -/
theorem fib_cassini_4 :
    intFib 3 * intFib 5 - intFib 4 * intFib 4 = negOnePow 4 := by decide

/-- Fibonacci Cassini at `n = 5`. -/
theorem fib_cassini_5 :
    intFib 4 * intFib 6 - intFib 5 * intFib 5 = negOnePow 5 := by decide

/-- Fibonacci Cassini at `n = 6`. -/
theorem fib_cassini_6 :
    intFib 5 * intFib 7 - intFib 6 * intFib 6 = negOnePow 6 := by decide

/-- Fibonacci Cassini at `n = 7`. -/
theorem fib_cassini_7 :
    intFib 6 * intFib 8 - intFib 7 * intFib 7 = negOnePow 7 := by decide

/-- Phase-space sum of squares at `n = 1`: `F_1^2 + F_2^2 = F_3`. -/
theorem phase_space_1 : fib 1 * fib 1 + fib 2 * fib 2 = fib 3 := by decide

/-- Phase-space sum of squares at `n = 2`: `F_2^2 + F_3^2 = F_5`. -/
theorem phase_space_2 : fib 2 * fib 2 + fib 3 * fib 3 = fib 5 := by decide

/-- Phase-space sum of squares at `n = 3`. -/
theorem phase_space_3 : fib 3 * fib 3 + fib 4 * fib 4 = fib 7 := by decide

/-- Phase-space sum of squares at `n = 4`. -/
theorem phase_space_4 : fib 4 * fib 4 + fib 5 * fib 5 = fib 9 := by decide

/-- Phase-space sum of squares at `n = 5`. -/
theorem phase_space_5 : fib 5 * fib 5 + fib 6 * fib 6 = fib 11 := by decide

/-- Phase-space sum of squares at `n = 6`. -/
theorem phase_space_6 : fib 6 * fib 6 + fib 7 * fib 7 = fib 13 := by decide

/-- Cross-Fibonacci coupling at `(m, n) = (2, 3)`:
    `F_2·F_3 + F_1·F_2 = F_4`. -/
theorem cross_fib_2_3 :
    fib 2 * fib 3 + fib 1 * fib 2 = fib 4 := by decide

/-- Cross-Fibonacci coupling at `(m, n) = (3, 4)`:
    `F_3·F_4 + F_2·F_3 = F_6`. -/
theorem cross_fib_3_4 :
    fib 3 * fib 4 + fib 2 * fib 3 = fib 6 := by decide

/-- Cross-Fibonacci coupling at `(m, n) = (4, 5)`:
    `F_4·F_5 + F_3·F_4 = F_8`. -/
theorem cross_fib_4_5 :
    fib 4 * fib 5 + fib 3 * fib 4 = fib 8 := by decide

/-- Cross-Fibonacci coupling at `(m, n) = (3, 5)`:
    `F_3·F_5 + F_2·F_4 = F_7`. -/
theorem cross_fib_3_5 :
    fib 3 * fib 5 + fib 2 * fib 4 = fib 7 := by decide

/-- Cross-Fibonacci coupling at `(m, n) = (4, 6)`:
    `F_4·F_6 + F_3·F_5 = F_9`. -/
theorem cross_fib_4_6 :
    fib 4 * fib 6 + fib 3 * fib 5 = fib 9 := by decide

/-! ## Group C --- Lucas--Fibonacci bridges -/

/-- Bragg Peak / Langlands S-duality at `n = 1`: `L_1 = F_0 + F_2`. -/
theorem bragg_peak_1 : lucas 1 = fib 0 + fib 2 := by decide

/-- Bragg Peak at `n = 2`. -/
theorem bragg_peak_2 : lucas 2 = fib 1 + fib 3 := by decide

/-- Bragg Peak at `n = 3`. -/
theorem bragg_peak_3 : lucas 3 = fib 2 + fib 4 := by decide

/-- Bragg Peak at `n = 4`. -/
theorem bragg_peak_4 : lucas 4 = fib 3 + fib 5 := by decide

/-- Bragg Peak at `n = 5`. -/
theorem bragg_peak_5 : lucas 5 = fib 4 + fib 6 := by decide

/-- Bragg Peak at `n = 6`. -/
theorem bragg_peak_6 : lucas 6 = fib 5 + fib 7 := by decide

/-- Bragg Peak at `n = 7`. -/
theorem bragg_peak_7 : lucas 7 = fib 6 + fib 8 := by decide

/-- Bragg Peak at `n = 8`. -/
theorem bragg_peak_8 : lucas 8 = fib 7 + fib 9 := by decide

/-- Topological Gap at `n = 1`: `L_1 = F_1 + 2·F_0 = 1`. -/
theorem topological_gap_1 : lucas 1 = fib 1 + 2 * fib 0 := by decide

/-- Topological Gap at `n = 2`: `L_2 = F_2 + 2·F_1 = 1 + 2 = 3`. -/
theorem topological_gap_2 : lucas 2 = fib 2 + 2 * fib 1 := by decide

/-- Topological Gap at `n = 3`. -/
theorem topological_gap_3 : lucas 3 = fib 3 + 2 * fib 2 := by decide

/-- Topological Gap at `n = 4`. -/
theorem topological_gap_4 : lucas 4 = fib 4 + 2 * fib 3 := by decide

/-- Topological Gap at `n = 5`. -/
theorem topological_gap_5 : lucas 5 = fib 5 + 2 * fib 4 := by decide

/-- Topological Gap at `n = 6`. -/
theorem topological_gap_6 : lucas 6 = fib 6 + 2 * fib 5 := by decide

/-- Topological Gap at `n = 7`. -/
theorem topological_gap_7 : lucas 7 = fib 7 + 2 * fib 6 := by decide

/-- Linear-tiling count on a `k`-edge strip. The number of domino-and-square
    tilings of a `1 × k` strip is `F_{k+1}`. We take that as the primitive
    `linear` from the ledger's "Circular Tiling Decomposition" row. -/
def linear (k : Nat) : Nat := fib (k + 1)

/-- Circular Tiling Decomposition at `n = 2`: `L_2 = linear 0 + linear 2`.
    `linear 0 = F_1 = 1` and `linear 2 = F_3 = 2`, so `L_2 = 3`. -/
theorem circular_tiling_2 : lucas 2 = linear 0 + linear 2 := by decide

/-- Circular Tiling Decomposition at `n = 3`. -/
theorem circular_tiling_3 : lucas 3 = linear 1 + linear 3 := by decide

/-- Circular Tiling Decomposition at `n = 4`. -/
theorem circular_tiling_4 : lucas 4 = linear 2 + linear 4 := by decide

/-- Circular Tiling Decomposition at `n = 5`. -/
theorem circular_tiling_5 : lucas 5 = linear 3 + linear 5 := by decide

/-- Circular Tiling Decomposition at `n = 6`. -/
theorem circular_tiling_6 : lucas 6 = linear 4 + linear 6 := by decide

/-- AdS/CFT holographic reconstruction at `n = 1`: `5·F_1 = L_0 + L_2`. -/
theorem adscft_1 : 5 * fib 1 = lucas 0 + lucas 2 := by decide

/-- AdS/CFT holographic reconstruction at `n = 2`. -/
theorem adscft_2 : 5 * fib 2 = lucas 1 + lucas 3 := by decide

/-- AdS/CFT holographic reconstruction at `n = 3`. -/
theorem adscft_3 : 5 * fib 3 = lucas 2 + lucas 4 := by decide

/-- AdS/CFT holographic reconstruction at `n = 4`. -/
theorem adscft_4 : 5 * fib 4 = lucas 3 + lucas 5 := by decide

/-- AdS/CFT holographic reconstruction at `n = 5`. -/
theorem adscft_5 : 5 * fib 5 = lucas 4 + lucas 6 := by decide

/-- AdS/CFT holographic reconstruction at `n = 6`. -/
theorem adscft_6 : 5 * fib 6 = lucas 5 + lucas 7 := by decide

/-- AdS/CFT holographic reconstruction at `n = 7`. -/
theorem adscft_7 : 5 * fib 7 = lucas 6 + lucas 8 := by decide

/-- √5 Cross-Product at even `n = 2`:
    `L_3 · F_2 + 2 = L_2 · F_3`.
    Numerically: `4·1 + 2 = 6 = 3·2`. -/
theorem sqrt5_cross_even_2 :
    intLucas 3 * intFib 2 + 2 = intLucas 2 * intFib 3 := by decide

/-- √5 Cross-Product at even `n = 4`:
    `L_5 · F_4 + 2 = L_4 · F_5`.
    Numerically: `11·3 + 2 = 35 = 7·5`. -/
theorem sqrt5_cross_even_4 :
    intLucas 5 * intFib 4 + 2 = intLucas 4 * intFib 5 := by decide

/-- √5 Cross-Product at even `n = 6`:
    `L_7 · F_6 + 2 = L_6 · F_7`. -/
theorem sqrt5_cross_even_6 :
    intLucas 7 * intFib 6 + 2 = intLucas 6 * intFib 7 := by decide

/-- √5 Cross-Product at odd `n = 1`:
    `L_1 · F_2 + 2 = L_2 · F_1`.
    Numerically: `1·1 + 2 = 3 = 3·1`. -/
theorem sqrt5_cross_odd_1 :
    intLucas 1 * intFib 2 + 2 = intLucas 2 * intFib 1 := by decide

/-- √5 Cross-Product at odd `n = 3`:
    `L_3 · F_4 + 2 = L_4 · F_3`.
    Numerically: `4·3 + 2 = 14 = 7·2`. -/
theorem sqrt5_cross_odd_3 :
    intLucas 3 * intFib 4 + 2 = intLucas 4 * intFib 3 := by decide

/-- √5 Cross-Product at odd `n = 5`:
    `L_5 · F_6 + 2 = L_6 · F_5`. -/
theorem sqrt5_cross_odd_5 :
    intLucas 5 * intFib 6 + 2 = intLucas 6 * intFib 5 := by decide

/-! ## Group D --- Pell discriminant identities -/

/-- Pell Discriminant (Even) at `n = 2`: `L_2^2 = 5·F_2^2 + 4`.
    Numerically: `9 = 5·1 + 4`. -/
theorem pell_even_2 : lucas 2 * lucas 2 = 5 * fib 2 * fib 2 + 4 := by decide

/-- Pell Discriminant (Even) at `n = 4`: `L_4^2 = 5·F_4^2 + 4`. -/
theorem pell_even_4 : lucas 4 * lucas 4 = 5 * fib 4 * fib 4 + 4 := by decide

/-- Pell Discriminant (Even) at `n = 6`. -/
theorem pell_even_6 : lucas 6 * lucas 6 = 5 * fib 6 * fib 6 + 4 := by decide

/-- Pell Discriminant (Odd) at `n = 1`: `5·F_1^2 = L_1^2 + 4`.
    Numerically: `5 = 1 + 4`. -/
theorem pell_odd_1 : 5 * fib 1 * fib 1 = lucas 1 * lucas 1 + 4 := by decide

/-- Pell Discriminant (Odd) at `n = 3`: `5·F_3^2 = L_3^2 + 4`. -/
theorem pell_odd_3 : 5 * fib 3 * fib 3 = lucas 3 * lucas 3 + 4 := by decide

/-- Pell Discriminant (Odd) at `n = 5`. -/
theorem pell_odd_5 : 5 * fib 5 * fib 5 = lucas 5 * lucas 5 + 4 := by decide

/-- Pell Discriminant (Odd) at `n = 7`. -/
theorem pell_odd_7 : 5 * fib 7 * fib 7 = lucas 7 * lucas 7 + 4 := by decide

/-! ## Group E --- E8 product-to-sum identities

The ledger rows read:

- **Odd**: `L_m · L_n + L_{m-n} = L_{m+n}` (when `m - n` is odd).
- **Even**: `L_m · L_n = L_{m+n} + L_{m-n}` (when `m - n` is even).

We check each at specific `(m, n)` pairs where the parity matches. -/

/-!  **Note.** The ledger's "Odd" row `L_m·L_n + L_{m-n} = L_{m+n}`
does not universally hold as stated. The classical product-to-sum
identity reads

  `L_m · L_n = L_{m+n} + (-1)^n · L_{m-n}`

for `m ≥ n`. When `m - n` is odd this becomes
`L_m · L_n = L_{m+n} - L_{m-n}`, i.e.
`L_m · L_n + L_{m-n} = L_{m+n}`, matching the ledger's odd row only
when `n` (not `m - n`) is odd. We check that form. When `n` is even
the identity becomes `L_m · L_n = L_{m+n} + L_{m-n}`, the ledger's
even row. The instances below use this corrected parity. -/

/-- E8 Product-to-Sum, odd `n`, at `(m, n) = (3, 1)`:
    `L_3·L_1 + L_2 = L_4`. Numerically: `4·1 + 3 = 7`. -/
theorem e8_odd_n_3_1 :
    lucas 3 * lucas 1 + lucas 2 = lucas 4 := by decide

/-- E8 Product-to-Sum, odd `n`, at `(m, n) = (4, 1)`:
    `L_4·L_1 + L_3 = L_5`. Numerically: `7·1 + 4 = 11`. -/
theorem e8_odd_n_4_1 :
    lucas 4 * lucas 1 + lucas 3 = lucas 5 := by decide

/-- E8 Product-to-Sum, odd `n`, at `(m, n) = (5, 3)`:
    `L_5·L_3 + L_2 = L_8`. Numerically: `11·4 + 3 = 47`. -/
theorem e8_odd_n_5_3 :
    lucas 5 * lucas 3 + lucas 2 = lucas 8 := by decide

/-- E8 Product-to-Sum, odd `n`, at `(m, n) = (6, 3)`:
    `L_6·L_3 + L_3 = L_9`. Numerically: `18·4 + 4 = 76`. -/
theorem e8_odd_n_6_3 :
    lucas 6 * lucas 3 + lucas 3 = lucas 9 := by decide

/-- E8 Product-to-Sum, even `n`, at `(m, n) = (4, 2)`:
    `L_4·L_2 = L_6 + L_2`. Numerically: `7·3 = 21 = 18 + 3`. -/
theorem e8_even_n_4_2 :
    lucas 4 * lucas 2 = lucas 6 + lucas 2 := by decide

/-- E8 Product-to-Sum, even `n`, at `(m, n) = (5, 2)`:
    `L_5·L_2 = L_7 + L_3`. Numerically: `11·3 = 33 = 29 + 4`. -/
theorem e8_even_n_5_2 :
    lucas 5 * lucas 2 = lucas 7 + lucas 3 := by decide

/-- E8 Product-to-Sum, even `n`, at `(m, n) = (6, 2)`:
    `L_6·L_2 = L_8 + L_4`. Numerically: `18·3 = 54 = 47 + 7`. -/
theorem e8_even_n_6_2 :
    lucas 6 * lucas 2 = lucas 8 + lucas 4 := by decide

/-- E8 Product-to-Sum, even `n`, at `(m, n) = (5, 4)`:
    `L_5·L_4 = L_9 + L_1`. Numerically: `11·7 = 77 = 76 + 1`. -/
theorem e8_even_n_5_4 :
    lucas 5 * lucas 4 = lucas 9 + lucas 1 := by decide

end FibLucasExtendedIdentities
end Gnosis
