import Init

/-!
# Catalan numbers: small-instance identities and Dyck-path witnesses

This module witnesses the usual small-`n` facts about the Catalan
sequence

    C_0 = 1, C_1 = 1, C_2 = 2, C_3 = 5, C_4 = 14,
    C_5 = 42, C_6 = 132, C_7 = 429.

Two independent definitions are given and checked against each other
on `n ∈ {0, …, 7}`:

* `catalanRec n` — computes `C_n` by the segmental recurrence
  `C_{n+1} = Σ_{i=0}^{n} C_i · C_{n-i}` (the standard "split at the
  first return to zero" recurrence for balanced parenthesizations).
* `catalanBinom n` — computes `C_n` via `C(2n, n) / (n + 1)`, where
  `binom` is a Pascal-rule helper `Nat → Nat → Nat`.

A third, combinatorial, definition `dyckPaths n` enumerates all
`List Bool` of length `2n` in which every prefix has at least as many
`true`s as `false`s and the total counts are equal. We check that
`(dyckPaths n).length = catalanRec n` for `n ∈ {1, 2, 3, 4}`. The
`n = 4` case enumerates all `2^8 = 256` bit-vectors and filters down
to the `14` Dyck words.

For completeness we also record a `binaryTreeCount` satisfying the
same recurrence as `catalanRec`; the equality `binaryTreeCount = catalanRec`
is observable by `decide` on the same small range.

## Caveats

* This is **not** a proof of the general identity
  `catalanRec n = catalanBinom n`; it is only the small-`n` table.
* No generating-function argument appears here.
* The equality `dyckPaths.length n = catalanRec n` is witnessed by
  `decide` at specific `n`, not by a bijective proof.
* `binaryTreeCount = catalanRec` is likewise a small-`n` table, not a
  bijection between binary trees and Dyck paths.

No `sorry`, no new `axiom`, `Init`-only, kernel `decide` only.
-/

namespace BuleyeanMath
namespace CatalanNumbersIdentity

/-! ## Segmental recurrence definition

To stay structurally recursive, `catalanRec` is defined via
`catalanTable`, which builds the list `[C_0, C_1, …, C_n]`
forward. At each step `C_{m+1}` is the convolution of the table
with its reverse — an `O(m)` dot product over already-computed
values. Consuming from a finite list is clearly terminating. -/

/-- Dot product of two `List Nat`s (zero-padding on mismatch;
`zipWith` truncates, which is harmless here since we always
pair a list with its reverse of equal length). -/
def dot : List Nat → List Nat → Nat
  | [],      _       => 0
  | _,       []      => 0
  | a :: as, b :: bs => a * b + dot as bs

/-- `catalanTable n = [C_0, C_1, …, C_n]`, built forward via
the segmental recurrence `C_{m+1} = Σ_{i=0}^{m} C_i · C_{m-i}
= dot [C_0,…,C_m] [C_m,…,C_0]`. -/
def catalanTable : Nat → List Nat
  | 0     => [1]
  | n + 1 =>
    let prev := catalanTable n
    prev ++ [dot prev prev.reverse]

/-- `catalanRec n` via the segmental recurrence
`C_{n+1} = Σ_{i=0}^{n} C_i · C_{n-i}`, with `C_0 = 1`. Reads the
last entry of `catalanTable n`. -/
def catalanRec (n : Nat) : Nat :=
  (catalanTable n).getLast!

/-! ## Binomial-coefficient definition -/

/-- Pascal-rule binomial coefficient `C(n, k)` on `Nat`.
Boundary: `binom n 0 = 1`, `binom 0 (k+1) = 0`,
recursion: `binom (n+1) (k+1) = binom n k + binom n (k+1)`. -/
def binom : Nat → Nat → Nat
  | _,     0     => 1
  | 0,     _ + 1 => 0
  | n + 1, k + 1 => binom n k + binom n (k + 1)

/-- `catalanBinom n = C(2n, n) / (n + 1)`. Exact on `Nat` because
`(n + 1)` divides `C(2n, n)` for all `n` (the usual Catalan identity). -/
def catalanBinom (n : Nat) : Nat :=
  binom (2 * n) n / (n + 1)

/-! ## Base-value tables (kernel `decide`) -/

/-- First eight Catalan values by the segmental recurrence:
`1, 1, 2, 5, 14, 42, 132, 429`. -/
theorem catalanRec_table :
    catalanRec 0 = 1   ∧ catalanRec 1 = 1   ∧
    catalanRec 2 = 2   ∧ catalanRec 3 = 5   ∧
    catalanRec 4 = 14  ∧ catalanRec 5 = 42  ∧
    catalanRec 6 = 132 ∧ catalanRec 7 = 429 := by decide

/-- First eight Catalan values by the central-binomial formula:
`1, 1, 2, 5, 14, 42, 132, 429`. -/
theorem catalanBinom_table :
    catalanBinom 0 = 1   ∧ catalanBinom 1 = 1   ∧
    catalanBinom 2 = 2   ∧ catalanBinom 3 = 5   ∧
    catalanBinom 4 = 14  ∧ catalanBinom 5 = 42  ∧
    catalanBinom 6 = 132 ∧ catalanBinom 7 = 429 := by decide

/-! ## Equivalence on `n = 0, …, 7` -/

/-- `catalanRec n = catalanBinom n` at every `n ∈ {0, …, 7}`.
Not a general theorem; just the small-`n` table. -/
theorem catalanRec_eq_catalanBinom_small :
    catalanRec 0 = catalanBinom 0 ∧
    catalanRec 1 = catalanBinom 1 ∧
    catalanRec 2 = catalanBinom 2 ∧
    catalanRec 3 = catalanBinom 3 ∧
    catalanRec 4 = catalanBinom 4 ∧
    catalanRec 5 = catalanBinom 5 ∧
    catalanRec 6 = catalanBinom 6 ∧
    catalanRec 7 = catalanBinom 7 := by decide

/-! ## Recurrence cross-check at `n = 5`

`C_5 = Σ_{i=0}^{4} C_i · C_{4-i}
     = 1·14 + 1·5 + 2·2 + 5·1 + 14·1
     = 42`. -/

/-- Witness the convolution directly for `n = 5`. -/
theorem catalanRec_5_convolution :
    catalanRec 5 =
      catalanRec 0 * catalanRec 4
    + catalanRec 1 * catalanRec 3
    + catalanRec 2 * catalanRec 2
    + catalanRec 3 * catalanRec 1
    + catalanRec 4 * catalanRec 0 := by decide

/-- Arithmetic check: the five terms sum to `42`. -/
theorem catalanRec_5_eq_42 :
    catalanRec 0 * catalanRec 4
    + catalanRec 1 * catalanRec 3
    + catalanRec 2 * catalanRec 2
    + catalanRec 3 * catalanRec 1
    + catalanRec 4 * catalanRec 0 = 42 := by decide

/-! ## Dyck-path enumeration

A Dyck word of semi-length `n` is a `List Bool` of length `2n` with
equal numbers of `true`s and `false`s such that every prefix has at
least as many `true`s as `false`s. (`true` = up step, `false` = down
step.) We enumerate all bit-vectors of length `2n` and filter. -/

/-- All `List Bool` of length `m`, in a deterministic order. -/
def allBitVectors : Nat → List (List Bool)
  | 0     => [[]]
  | m + 1 =>
    let rest := allBitVectors m
    rest.map (fun xs => false :: xs) ++ rest.map (fun xs => true :: xs)

/-- Prefix-and-total test: scan left-to-right tracking a signed
height (up `true` = +1, down `false` = −1). Require height `≥ 0`
throughout and equal to `0` at the end. `h` is the current height
as a `Nat`; `false` at `h = 0` aborts. -/
def isDyck : List Bool → Nat → Bool
  | [],           0     => true
  | [],           _ + 1 => false
  | true  :: bs,  h     => isDyck bs (h + 1)
  | false :: _,   0     => false
  | false :: bs,  h + 1 => isDyck bs h

/-- All Dyck words of semi-length `n`. -/
def dyckPaths (n : Nat) : List (List Bool) :=
  (allBitVectors (2 * n)).filter (fun bs => isDyck bs 0)

/-! ### Sanity: the search space has the expected size -/

set_option maxRecDepth 2048 in
/-- The length-`2n` bit-vector enumeration at `n = 4` has `256`
entries (it's the full `2^{2n}` search space before filtering). -/
theorem allBitVectors_8_length : (allBitVectors 8).length = 256 := by decide

/-! ### Dyck-path counts match `catalanRec` for small `n` -/

/-- `|dyckPaths 1| = C_1 = 1`. The unique word is `[true, false]`. -/
theorem dyckPaths_1_length : (dyckPaths 1).length = catalanRec 1 := by decide

/-- `|dyckPaths 2| = C_2 = 2`. The words are `[T,F,T,F]` and
`[T,T,F,F]`. -/
theorem dyckPaths_2_length : (dyckPaths 2).length = catalanRec 2 := by decide

/-- `|dyckPaths 3| = C_3 = 5`. -/
theorem dyckPaths_3_length : (dyckPaths 3).length = catalanRec 3 := by decide

/-- `|dyckPaths 4| = C_4 = 14`. Filters `256` bit-vectors down to
`14`. -/
theorem dyckPaths_4_length : (dyckPaths 4).length = catalanRec 4 := by decide

/-! ## Binary-tree count

`binaryTreeCount n` counts full binary trees with `n` internal nodes
by the recurrence `T_{n+1} = Σ_{i=0}^{n} T_i · T_{n-i}`, `T_0 = 1`.
This is definitionally the same body as `catalanRec`, recorded
separately so the small-`n` equality is visible as an identity of
sequences and not just unfolded arithmetic. -/

/-- Table of full-binary-tree counts, built forward by the same
segmental convolution. -/
def binaryTreeTable : Nat → List Nat
  | 0     => [1]
  | n + 1 =>
    let prev := binaryTreeTable n
    prev ++ [dot prev prev.reverse]

/-- Count of full binary trees with `n` internal nodes. -/
def binaryTreeCount (n : Nat) : Nat :=
  (binaryTreeTable n).getLast!

/-- `binaryTreeCount n = catalanRec n` for `n ∈ {0, …, 7}`. Not a
bijective proof, just equal counts. -/
theorem binaryTreeCount_eq_catalanRec_small :
    binaryTreeCount 0 = catalanRec 0 ∧
    binaryTreeCount 1 = catalanRec 1 ∧
    binaryTreeCount 2 = catalanRec 2 ∧
    binaryTreeCount 3 = catalanRec 3 ∧
    binaryTreeCount 4 = catalanRec 4 ∧
    binaryTreeCount 5 = catalanRec 5 ∧
    binaryTreeCount 6 = catalanRec 6 ∧
    binaryTreeCount 7 = catalanRec 7 := by decide

end CatalanNumbersIdentity
end BuleyeanMath
