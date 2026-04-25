import Init

/-!
# Hamming and Singleton bounds on concrete small codes

This module witnesses the Hamming packing bound and the Singleton
bound from coding theory on concrete parameter sets. We formalize a
few small codes at the codeword level, compute their minimum Hamming
distance by enumeration, and verify the bounds by `decide`.

The results are computational in character: we do not prove the
general Singleton bound `d ≤ n - k + 1` nor the general Hamming
packing bound `|C| · V_q(n, t) ≤ q^n`. We verify those inequalities
on fixed instances.

## Codes formalized

* Repetition code `[3, 1, 3]_2` — explicit codeword list
  `[[0,0,0], [1,1,1]]` over `Fin 2`. Minimum distance computed by
  pairwise Hamming distance.
* Parity-check code `[4, 3, 2]_2` — parameter-level only.
* Hamming code `[7, 4, 3]_2` — parameter-level only.
* Ternary MDS code `[3, 2, 2]_3` — parameter-level only.

## Bounds verified

* Singleton `d ≤ n - k + 1` on all four above.
* Hamming packing `|C| · V_q(n, t) ≤ q^n` on `[7, 4, 3]_2` with
  `t = 1` and on `[15, 11, 3]_2` with `t = 1`. Both are tight
  (perfect codes), so equality holds.

No `sorry`, no new `axiom`, `Init`-only. All proofs close by kernel
`decide`.
-/

namespace BuleyeanMath
namespace HammingSingletonBound

/-! ## Hamming distance on fixed-length symbol lists

We represent codewords as `List Nat`, interpreting each entry as a
symbol from `Fin q`. The distance is the number of positions where
the two words differ; ragged-length comparisons stop at the shorter
word (we only call these on codewords of matching length, so the
edge cases never fire). -/

/-- Hamming distance between two symbol lists: count of positions
where they differ. Stops at the shorter list. -/
def hammingDist : List Nat → List Nat → Nat
  | [], _ => 0
  | _, [] => 0
  | x :: xs, y :: ys =>
    (if x = y then 0 else 1) + hammingDist xs ys

/-- Minimum Hamming distance between a codeword `c` and every other
codeword in `cs`. Returns `default` if `cs` is empty. -/
def minDistFrom (c : List Nat) (default : Nat) : List (List Nat) → Nat
  | [] => default
  | c' :: rest =>
    if c = c' then minDistFrom c default rest
    else
      let d := hammingDist c c'
      let m := minDistFrom c default rest
      if d < m then d else m

/-- Fold the minimum over every pair `(c, c')` with `c ≠ c'`.
Starts with a large default so that any real distance wins. -/
def minDistAux (all : List (List Nat)) (default : Nat)
    : List (List Nat) → Nat
  | [] => default
  | c :: rest =>
    let here := minDistFrom c default all
    let there := minDistAux all default rest
    if here < there then here else there

/-- Minimum Hamming distance of a codebook, using `default` as the
"no other codeword" sentinel. For a codebook with at least two
distinct codewords this returns the true minimum distance. -/
def minDist (code : List (List Nat)) (default : Nat) : Nat :=
  minDistAux code default code

/-! ## Binomial coefficients and Hamming ball volumes -/

/-- Binomial coefficient `C(n, k)` by Pascal's recurrence. -/
def binom : Nat → Nat → Nat
  | _, 0 => 1
  | 0, Nat.succ _ => 0
  | Nat.succ n, Nat.succ k => binom n k + binom n (Nat.succ k)

/-- Natural-number power `b^e`. Defined locally so the module stays
`Init`-only across toolchain versions. -/
def natPow (b : Nat) : Nat → Nat
  | 0 => 1
  | Nat.succ e => b * natPow b e

/-- Partial Hamming-ball volume helper: sum of `C(n, i) · (q-1)^i`
for `i` from `0` up to `fuel`, evaluated against a fixed ceiling
`t`. We terminate when `fuel` runs out or the index exceeds `t`. -/
def hammingBallVolAux (n q t : Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | Nat.succ fuel, i =>
    if i > t then 0
    else
      binom n i * natPow (q - 1) i
        + hammingBallVolAux n q t fuel (Nat.succ i)

/-- Hamming-ball volume `V_q(n, t) = Σ_{i=0}^{t} C(n, i) · (q-1)^i`. -/
def hammingBallVol (q n t : Nat) : Nat :=
  hammingBallVolAux n q t (Nat.succ t) 0

/-! ## Explicit codes

We represent codewords as `List Nat`. Callers are responsible for
only using symbols in `[0, q)`. -/

/-- Binary repetition code of length 3: `C = {000, 111}`. -/
def repetitionCode3 : List (List Nat) :=
  [ [0, 0, 0]
  , [1, 1, 1]
  ]

/-! ## Singleton bound on concrete codes

For an `[n, k, d]_q` code, the Singleton bound is `d ≤ n - k + 1`.
We verify this on four small instances. -/

/-- Singleton bound for the binary repetition code `[3, 1, 3]_2`.
The minimum distance is `3`, matching `n - k + 1 = 3 - 1 + 1 = 3`.
This is tight. Proved by computing `minDist` explicitly over the
codebook and comparing. -/
theorem singleton_repetition_3_1_3 :
    minDist repetitionCode3 4 ≤ 3 - 1 + 1 := by decide

/-- The repetition code `[3, 1, 3]_2` saturates the Singleton bound:
`minDist = n - k + 1 = 3`. -/
theorem singleton_repetition_3_1_3_tight :
    minDist repetitionCode3 4 = 3 - 1 + 1 := by decide

/-- Singleton bound for the binary parity-check code `[4, 3, 2]_2`.
Parameter-level check: `d = 2 ≤ n - k + 1 = 4 - 3 + 1 = 2`. Tight. -/
theorem singleton_parity_4_3_2 : (2 : Nat) ≤ 4 - 3 + 1 := by decide

/-- Singleton bound for the binary Hamming code `[7, 4, 3]_2`.
Parameter-level check: `d = 3 ≤ n - k + 1 = 7 - 4 + 1 = 4`. Strict. -/
theorem singleton_hamming_7_4_3 : (3 : Nat) ≤ 7 - 4 + 1 := by decide

/-- Singleton bound for the ternary MDS code `[3, 2, 2]_3`.
Parameter-level check: `d = 2 ≤ n - k + 1 = 3 - 2 + 1 = 2`. Tight. -/
theorem singleton_mds_ternary_3_2_2 : (2 : Nat) ≤ 3 - 2 + 1 := by decide

/-! ## Hamming packing bound on concrete codes

For a `q`-ary code `C` of length `n` correcting `t` errors,
`|C| · V_q(n, t) ≤ q^n` where `V_q(n, t)` is the Hamming-ball
volume. Perfect codes saturate the bound.
-/

/-- Hamming ball volume `V_2(7, 1) = 1 + 7 = 8`. -/
theorem hamming_ball_vol_2_7_1 : hammingBallVol 2 7 1 = 8 := by decide

/-- Hamming ball volume `V_2(15, 1) = 1 + 15 = 16`. -/
theorem hamming_ball_vol_2_15_1 : hammingBallVol 2 15 1 = 16 := by decide

/-- Hamming packing bound for `[7, 4, 3]_2`:
`|C| · V_2(7, 1) = 16 · 8 = 128 = 2^7`. Perfect (tight). -/
theorem hamming_packing_7_4_3 :
    natPow 2 4 * hammingBallVol 2 7 1 ≤ natPow 2 7 := by decide

/-- The `[7, 4, 3]_2` Hamming code saturates the packing bound. -/
theorem hamming_packing_7_4_3_tight :
    natPow 2 4 * hammingBallVol 2 7 1 = natPow 2 7 := by decide

/-- Hamming packing bound for `[15, 11, 3]_2`:
`|C| · V_2(15, 1) = 2048 · 16 = 32768 = 2^15`. Perfect (tight). -/
theorem hamming_packing_15_11_3 :
    natPow 2 11 * hammingBallVol 2 15 1 ≤ natPow 2 15 := by decide

/-- The `[15, 11, 3]_2` Hamming code saturates the packing bound. -/
theorem hamming_packing_15_11_3_tight :
    natPow 2 11 * hammingBallVol 2 15 1 = natPow 2 15 := by decide

/-! ## Sanity checks on binomial coefficients and powers -/

/-- `C(7, 0) = 1`, `C(7, 1) = 7`, `C(7, 2) = 21`, `C(7, 3) = 35`. -/
theorem binom_7_table :
    binom 7 0 = 1 ∧ binom 7 1 = 7 ∧ binom 7 2 = 21 ∧ binom 7 3 = 35 := by
  decide

/-- `C(15, 0) = 1`, `C(15, 1) = 15`, `C(15, 2) = 105`. -/
theorem binom_15_table :
    binom 15 0 = 1 ∧ binom 15 1 = 15 ∧ binom 15 2 = 105 := by decide

/-- `2^4 = 16`, `2^7 = 128`, `2^11 = 2048`, `2^15 = 32768`. -/
theorem natPow_2_table :
    natPow 2 4 = 16 ∧ natPow 2 7 = 128 ∧
    natPow 2 11 = 2048 ∧ natPow 2 15 = 32768 := by decide

/-! ## Codebook-level sanity for the repetition code -/

/-- The repetition code has two codewords. -/
theorem repetitionCode3_size : repetitionCode3.length = 2 := by decide

/-- Pairwise Hamming distances in the repetition code. -/
theorem repetitionCode3_pairwise :
    hammingDist [0, 0, 0] [1, 1, 1] = 3 ∧
    hammingDist [1, 1, 1] [0, 0, 0] = 3 := by decide

end HammingSingletonBound
end BuleyeanMath
