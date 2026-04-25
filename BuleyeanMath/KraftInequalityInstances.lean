import Init

/-!
# Kraft inequality on concrete prefix codes

This module witnesses Kraft's inequality from information theory on a
handful of concrete codeword-length profiles and on one explicit
binary prefix code given as `List (List Bool)`.

Kraft's inequality states that for a binary prefix code with
codeword lengths `l_1, ..., l_n`,

  `Σ 2^(-l_i) ≤ 1`.

Because `Init` offers no rationals, we clear the fractions. Let
`L = max l_i`. The inequality rescales to

  `Σ 2^(L - l_i) ≤ 2^L`

over `Nat`, which is what we actually verify.

We do *not* prove the general Kraft theorem (for every prefix code
the rescaled sum is bounded by `2^L`). We do *not* prove the source
coding theorem or any logarithmic statement. Instead we compute the
sum on four fixed length profiles and `decide` the inequality, and
we check one explicit codebook in `List (List Bool)`.

## Length profiles formalized

* Huffman-style `[1, 2, 3, 3]` — tight, `Σ 2^(3-l) = 8 = 2^3`.
* Non-optimal `[2, 2, 3, 4]` — slack, `Σ 2^(4-l) = 11 ≤ 16 = 2^4`.
* Uniform `[3, 3, 3, 3, 3, 3, 3, 3]` — tight, `Σ 2^0 = 8 = 2^3`.
* Anti-Kraft `[1, 1, 2]` — violates the inequality,
  `Σ 2^(2-l) = 5 > 4 = 2^2`. We prove the *negation*.

## Explicit codebook

One Huffman tree `C = [[false], [true, false], [true, true, false],
[true, true, true]]` with lengths `[1, 2, 3, 3]`. We verify that it
is a prefix code (no codeword is a prefix of another) and that its
length profile satisfies Kraft. A McMillan-flavoured corollary
restates the bound for this uniquely decodable (in fact prefix)
codebook.

No `sorry`, no new `axiom`, `Init`-only. All proofs close by kernel
`decide`.
-/

namespace BuleyeanMath
namespace KraftInequalityInstances

/-! ## Natural-number power

Defined locally so the module stays `Init`-only across toolchain
versions. -/

/-- Natural-number power `b^e` by recursion on `e`. -/
def natPow (b : Nat) : Nat → Nat
  | 0 => 1
  | Nat.succ e => b * natPow b e

/-! ## Maximum of a length list -/

/-- Maximum of a list of `Nat`; returns `0` on the empty list. -/
def listMax : List Nat → Nat
  | [] => 0
  | x :: xs =>
    let m := listMax xs
    if x < m then m else x

/-! ## Rescaled Kraft sum

For lengths `ls` and ceiling `L`, compute `Σ 2^(L - l)`. Callers
should pass `L = listMax ls` so no subtraction underflows outside the
intended range; if some `l > L` the `Nat` subtraction truncates to
`0`, contributing `2^0 = 1` to the sum, which is fine for the kinds
of `decide` checks below. -/

/-- Rescaled Kraft sum `Σ 2^(L - l)` over a length list. -/
def kraftSum (L : Nat) : List Nat → Nat
  | [] => 0
  | l :: ls => natPow 2 (L - l) + kraftSum L ls

/-! ## Prefix relation and prefix-code predicate on `List Bool`

We spell out `isPrefix` and the "no codeword is a prefix of another"
predicate by hand so this module stays `Init`-only. -/

/-- `isPrefix p w` holds iff the list `p` is a prefix of `w`. -/
def isPrefix : List Bool → List Bool → Bool
  | [], _ => true
  | _ :: _, [] => false
  | x :: xs, y :: ys =>
    if x = y then isPrefix xs ys else false

/-- `noneIsPrefix c cs` holds iff `c` is neither a proper prefix of
nor equal to any element of `cs`, and symmetrically no element of
`cs` is a prefix of `c`. -/
def noneIsPrefix (c : List Bool) : List (List Bool) → Bool
  | [] => true
  | c' :: rest =>
    if isPrefix c c' then false
    else if isPrefix c' c then false
    else noneIsPrefix c rest

/-- `isPrefixCode cs` holds iff no codeword in `cs` is a prefix of
another. Decidable by structural recursion. -/
def isPrefixCode : List (List Bool) → Bool
  | [] => true
  | c :: rest =>
    if noneIsPrefix c rest then isPrefixCode rest else false

/-- Length profile of a binary codebook: the list of codeword
lengths, in order. -/
def codeLengths : List (List Bool) → List Nat
  | [] => []
  | c :: rest => c.length :: codeLengths rest

/-! ## Length-profile instances of Kraft

Each theorem computes `kraftSum L ls` on a fixed profile and
`decide`s the rescaled inequality. -/

/-- Huffman-style optimal profile `[1, 2, 3, 3]`: rescaled Kraft sum
at `L = 3` equals `2^3`, saturating the bound. -/
theorem kraft_huffman_1_2_3_3_sum :
    kraftSum 3 [1, 2, 3, 3] = natPow 2 3 := by decide

/-- Kraft for `[1, 2, 3, 3]`: `Σ 2^(3-l) ≤ 2^3`. Tight. -/
theorem kraft_huffman_1_2_3_3 :
    kraftSum 3 [1, 2, 3, 3] ≤ natPow 2 3 := by decide

/-- Non-optimal profile `[2, 2, 3, 4]`: rescaled Kraft sum at
`L = 4` equals `11`. -/
theorem kraft_nonopt_2_2_3_4_sum :
    kraftSum 4 [2, 2, 3, 4] = 11 := by decide

/-- Kraft for `[2, 2, 3, 4]`: `Σ 2^(4-l) = 11 ≤ 16 = 2^4`. Strict. -/
theorem kraft_nonopt_2_2_3_4 :
    kraftSum 4 [2, 2, 3, 4] ≤ natPow 2 4 := by decide

/-- Uniform-length profile `[3, 3, 3, 3, 3, 3, 3, 3]`: rescaled
Kraft sum at `L = 3` equals `8 = 2^3`. -/
theorem kraft_uniform_3x8_sum :
    kraftSum 3 [3, 3, 3, 3, 3, 3, 3, 3] = natPow 2 3 := by decide

/-- Kraft for the uniform profile `[3, 3, 3, 3, 3, 3, 3, 3]`:
`Σ 2^0 = 8 = 2^3`. Tight. -/
theorem kraft_uniform_3x8 :
    kraftSum 3 [3, 3, 3, 3, 3, 3, 3, 3] ≤ natPow 2 3 := by decide

/-- Anti-Kraft profile `[1, 1, 2]`: rescaled sum at `L = 2` equals
`5`, which exceeds `2^2 = 4`. -/
theorem kraft_antikraft_1_1_2_sum :
    kraftSum 2 [1, 1, 2] = 5 := by decide

/-- Anti-Kraft for `[1, 1, 2]`: the rescaled inequality *fails*.
`Σ 2^(2-l) = 5 > 4 = 2^2`, so no binary prefix code can realise
this length profile. -/
theorem kraft_antikraft_1_1_2_fails :
    ¬ (kraftSum 2 [1, 1, 2] ≤ natPow 2 2) := by decide

/-- Strict form of the anti-Kraft violation: the rescaled sum is
strictly greater than `2^2`. -/
theorem kraft_antikraft_1_1_2_strict :
    natPow 2 2 < kraftSum 2 [1, 1, 2] := by decide

/-! ## Explicit Huffman codebook over `Bool`

`huffmanCode` is a prefix code with lengths `[1, 2, 3, 3]`. We
verify the prefix-code predicate by `decide`, extract the length
profile, and check Kraft on it. -/

/-- Explicit Huffman-tree codebook with length profile `[1, 2, 3, 3]`. -/
def huffmanCode : List (List Bool) :=
  [ [false]
  , [true, false]
  , [true, true, false]
  , [true, true, true]
  ]

/-- `huffmanCode` is a prefix code: no codeword is a prefix of
another. -/
theorem huffmanCode_isPrefixCode : isPrefixCode huffmanCode = true := by decide

/-- The length profile of `huffmanCode` is `[1, 2, 3, 3]`. -/
theorem huffmanCode_lengths :
    codeLengths huffmanCode = [1, 2, 3, 3] := by decide

/-- Kraft on the explicit Huffman codebook: rescaled sum at `L = 3`
saturates `2^3`. -/
theorem huffmanCode_kraft_tight :
    kraftSum 3 (codeLengths huffmanCode) = natPow 2 3 := by decide

/-- Kraft inequality witnessed on the explicit Huffman codebook. -/
theorem huffmanCode_kraft :
    kraftSum 3 (codeLengths huffmanCode) ≤ natPow 2 3 := by decide

/-! ## McMillan-flavoured corollary

McMillan extends Kraft from prefix codes to uniquely decodable
codes. Every prefix code is uniquely decodable, so on a concrete
prefix code McMillan is strictly weaker than Kraft and the same
numerical bound applies. We restate the bound for `huffmanCode`
under the explicit prefix-code hypothesis. -/

/-- McMillan corollary on `huffmanCode`. Given that `huffmanCode` is
a prefix code (hence uniquely decodable), the rescaled Kraft bound
holds for its length profile. The hypothesis is discharged by
`huffmanCode_isPrefixCode`. -/
theorem huffmanCode_mcmillan
    (_h : isPrefixCode huffmanCode = true) :
    kraftSum 3 (codeLengths huffmanCode) ≤ natPow 2 3 := by
  -- The hypothesis certifies unique decodability of this codebook;
  -- the numerical bound is the Kraft inequality for its length
  -- profile, which we have already decided.
  exact huffmanCode_kraft

/-! ## Sanity checks -/

/-- `natPow 2` small table. -/
theorem natPow_2_small :
    natPow 2 0 = 1 ∧ natPow 2 1 = 2 ∧ natPow 2 2 = 4 ∧
    natPow 2 3 = 8 ∧ natPow 2 4 = 16 := by decide

/-- `listMax` on the Huffman length profile returns `3`. -/
theorem listMax_huffman_profile :
    listMax [1, 2, 3, 3] = 3 := by decide

/-- `listMax` on the anti-Kraft profile returns `2`. -/
theorem listMax_antikraft_profile :
    listMax [1, 1, 2] = 2 := by decide

/-- `huffmanCode` has four codewords. -/
theorem huffmanCode_size : huffmanCode.length = 4 := by decide

/-- `isPrefix` sanity: `[false]` is a prefix of `[false, true]`. -/
theorem isPrefix_false_ft : isPrefix [false] [false, true] = true := by decide

/-- `isPrefix` sanity: `[true]` is not a prefix of `[false, true]`. -/
theorem isPrefix_true_ft : isPrefix [true] [false, true] = false := by decide

/-- `isPrefix` sanity: empty list is a prefix of everything. -/
theorem isPrefix_nil : isPrefix [] [true, false, true] = true := by decide

/-- A codebook with a proper prefix pair is *not* a prefix code. -/
theorem notPrefixCode_example :
    isPrefixCode [[false], [false, true]] = false := by decide

end KraftInequalityInstances
end BuleyeanMath
