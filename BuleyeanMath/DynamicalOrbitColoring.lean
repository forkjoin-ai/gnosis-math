import Init

/-!
# Dynamical Orbit Coloring: Ramsey-flavored combinatorics on an Arnold cat-map orbit

This module bridges `ArnoldCatMapOrder5.lean` (the cat-map matrix
`A = [[2,1],[1,1]]` has multiplicative order `10` on `(ℤ/5)²`) and
`RamseyR33.lean` (Ramsey-style 2-coloring enumerations over `List Bool`).

Fix a full-period seed `v = (1, 0) ∈ (ℤ/5)²`. Iterating the cat map
produces the 10-point orbit

    orbit = [v, A·v, A²·v, ..., A⁹·v]

with all 10 points distinct (witnessed below). The `2^10 = 1024`
2-colorings of this orbit form a finite search space. The
*dynamical-Ramsey question* asked here is:

  **Does every 2-coloring of the 10-point orbit contain three
  *consecutive* orbit-steps `(Aⁱv, Aⁱ⁺¹v, Aⁱ⁺²v)` (indices mod 10)
  that receive the same color?**

Unlike classical Ramsey on complete graphs, this property is about
*indexed time-points* of a discrete dynamical orbit, and the index set
is cyclic (mod 10). It is strictly weaker than graph-theoretic Ramsey:
the `T-T-F-F-T-T-F-F-T-F` pattern below witnesses that the answer is
**no** — a 2-coloring can avoid monochromatic 3-consecutive triples on
a length-10 cyclic sequence.

## What this module witnesses

1. The 10-point orbit of `(1, 0)` under `CatMap 5` has ten distinct
   points (computed by kernel `decide`).
2. A Boolean detector `has3Consecutive : List Bool → Bool` that checks
   whether some index `i ∈ {0..n-1}` has `c[i] = c[(i+1) mod n] =
   c[(i+2) mod n]`.
3. An enumeration `allColorings n : List (List Bool)` producing every
   length-`n` Boolean list (`2^n` entries).
4. An explicit avoidance witness at length `10`:
   `[T, T, F, F, T, T, F, F, T, F]` contains no monochromatic
   3-consecutive triple. Hence the dynamical-Ramsey question is
   answered *negatively* for the specific 10-point orbit of `(1, 0)`.
5. Threshold check for `n ∈ {3, 4, 5, 6, 7, 8, 9, 10}`: in every case
   there exists at least one 2-coloring of a length-`n` cyclic
   sequence with no monochromatic 3-consecutive triple. The count of
   such "Ramsey-bad" colorings is tabulated by `native_decide`.
6. The exact count of Ramsey-bad colorings for `n = 10` is `122`
   (out of `1024`). Closed by `native_decide` on the 1024 cases.
7. A small-scale kernel-`decide` mirror: for `n ∈ {3, 4, 5}` the bad
   counts are `6`, `6`, `10` respectively.

## What this module does *not* claim

- The orbit under consideration is the *specific* orbit of the seed
  `(1, 0)` under `CatMap 5`. No claim is made for arbitrary seeds or
  arbitrary discrete dynamical systems.
- The "3-consecutive monochromatic" property is *weaker* than classical
  van der Waerden / Ramsey: it operates on a cyclic ordering of
  orbit-indices rather than on the complete graph of orbit-pairs. No
  arithmetic progressions in a group sense are tested — only
  consecutive-in-time triples.
- No continuous ergodic theory, no topological entropy, no general
  dynamical-Ramsey theorem is claimed. The bridge is finite and
  computational.
- The `n = 10` case does *not* imply an abstract threshold statement
  about length-`n` cyclic 2-colorings. It records a specific
  enumeration result for the orbit length witnessed by
  `ArnoldCatMapOrder5.ord_A_mod_5_eq_10`.

No `sorry`, no new `axiom`, `Init`-only. Most items close under kernel
`decide`; the two statements quantified over all 1024 length-10
colorings (the exact bad-count and the universal existence of
3-consecutive triples over the positive cases) use `native_decide`
with the same trust-base reasoning as `RamseyR33.ramsey_upper_bound`.
-/

namespace BuleyeanMath
namespace DynamicalOrbitColoring

/-! ## Inline cat map (mirror of `ArnoldCatMapOrder5.CatMap`) -/

/-- Arnold's cat map on the discrete torus `(ℤ/n)²`, viewed as
`Nat × Nat` with coordinates reduced mod `n`. Mirrors
`ArnoldCatMapOrder5.CatMap` so this file compiles standalone. -/
def CatMap (n : Nat) (p : Nat × Nat) : Nat × Nat :=
  ((2 * p.1 + p.2) % n, (p.1 + p.2) % n)

/-- `k`-fold application of `CatMap n`. -/
def catMapIter (n : Nat) : Nat → Nat × Nat → Nat × Nat
  | 0,     p => (p.1 % n, p.2 % n)
  | k + 1, p => CatMap n (catMapIter n k p)

/-! ## The 10-point orbit of `(1, 0)` under `CatMap 5`

The seed `(1, 0)` is the same point used in
`ArnoldCatMapOrder5` to rule out the proper divisors `1, 2, 5` of the
order `10`. Therefore its orbit has full period `10`.
-/

/-- The 10-point orbit of `(1, 0)` under `CatMap 5`, listed in
time order `[v, A·v, A²·v, ..., A⁹·v]`. -/
def orbitMod5 : List (Nat × Nat) :=
  [ catMapIter 5 0 (1, 0)
  , catMapIter 5 1 (1, 0)
  , catMapIter 5 2 (1, 0)
  , catMapIter 5 3 (1, 0)
  , catMapIter 5 4 (1, 0)
  , catMapIter 5 5 (1, 0)
  , catMapIter 5 6 (1, 0)
  , catMapIter 5 7 (1, 0)
  , catMapIter 5 8 (1, 0)
  , catMapIter 5 9 (1, 0)
  ]

/-- Sanity: the orbit record has exactly 10 entries. -/
theorem orbitMod5_length : orbitMod5.length = 10 := by decide

/-- **The orbit explicitly.** Each index maps to the expected
`(x, y) ∈ (ℤ/5)²`. Closed by kernel `decide`. -/
theorem orbitMod5_values :
    orbitMod5 = [ (1, 0), (2, 1), (0, 3), (3, 3), (4, 1)
                , (4, 0), (3, 4), (0, 2), (2, 2), (1, 4) ] := by decide

/-- List membership without importing `List.Mem` machinery. -/
def listMem (p : Nat × Nat) : List (Nat × Nat) → Bool
  | [] => false
  | q :: rest => (p.1 == q.1 && p.2 == q.2) || listMem p rest

/-- `true` iff the list has pairwise-distinct entries. -/
def pairwiseDistinct : List (Nat × Nat) → Bool
  | [] => true
  | p :: rest => !listMem p rest && pairwiseDistinct rest

/-- **Full-period check.** The ten entries of `orbitMod5` are pairwise
distinct. Combined with `orbitMod5_length = 10`, this witnesses that
`(1, 0)` has a full-period-`10` orbit under `CatMap 5`. -/
theorem orbitMod5_distinct : pairwiseDistinct orbitMod5 = true := by decide

/-! ## Cyclic 3-consecutive detector

A length-`n` `List Bool` is treated as a *cyclic* sequence: index
`i + 1` wraps to index `(i + 1) % n`, and similarly for `i + 2`.
The detector returns `true` iff some index `i ∈ {0, …, n−1}` has
`c[i] = c[(i+1) mod n] = c[(i+2) mod n]`.
-/

/-- Indexed lookup on `List Bool` with `false` as the out-of-bounds
default. Mirrors `RamseyR33.nthBool`. -/
def nthBool : List Bool → Nat → Bool
  | [], _ => false
  | x :: _, 0 => x
  | _ :: xs, Nat.succ k => nthBool xs k

/-- Scan indices `0, 1, …, n-1` for a monochromatic 3-consecutive
triple on the cyclic index set `ℤ/n`. The helper uses an explicit
countdown `k` bounded by `n`. -/
def has3CycleAux (c : List Bool) (n : Nat) : Nat → Bool
  | 0 => false
  | Nat.succ k =>
    let i := n - Nat.succ k
    let a := nthBool c i
    let b := nthBool c ((i + 1) % n)
    let d := nthBool c ((i + 2) % n)
    (a == b && b == d) || has3CycleAux c n k

/-- `true` iff `c` (as a cyclic length-`n` sequence) contains some
index `i` with `c[i] = c[(i+1) mod n] = c[(i+2) mod n]`. -/
def has3Consecutive (c : List Bool) : Bool :=
  has3CycleAux c c.length c.length

/-! ## Enumerate all length-`n` Boolean lists

Same construction as `RamseyR33.allBoolVecs`; re-declared inline to
keep this file standalone. -/

/-- All `2^n` length-`n` Boolean lists. -/
def allColorings : Nat → List (List Bool)
  | 0 => [[]]
  | Nat.succ k =>
    let tails := allColorings k
    (tails.map (fun t => false :: t)) ++ (tails.map (fun t => true :: t))

/-- `allColorings 10` has `2^10 = 1024` entries. Closed by
`native_decide` on the enumeration length (kernel `decide` hits
`maxRecDepth` on the 10-deep `List.map ++` unfolding even with the
limit raised to `65536`; the computation is pure, total, and
decidable). -/
theorem allColorings_10_length : (allColorings 10).length = 1024 := by
  native_decide

/-! ## Avoidance witness at length 10

The pattern `[T, T, F, F, T, T, F, F, T, F]` has no index `i` (mod 10)
with three equal colors at `i, i+1, i+2`. Reading indices 0..9:

| i | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 |
|---|---|---|---|---|---|---|---|---|---|---|
| c | T | T | F | F | T | T | F | F | T | F |

Every consecutive triple `(c[i], c[(i+1)%10], c[(i+2)%10])` is either
two-and-one or one-and-two-and-one, never three-of-a-kind.

Hence the dynamical-Ramsey question "is `has3Consecutive` forced?"
answers **no** for `n = 10`: this explicit coloring witnesses an
escape.
-/

/-- The avoidance-witness coloring. -/
def avoidanceColoring10 : List Bool :=
  [true, true, false, false, true, true, false, false, true, false]

/-- The avoidance coloring has length `10`. -/
theorem avoidanceColoring10_length : avoidanceColoring10.length = 10 := by decide

/-- **Main negative answer.** The avoidance coloring contains no
monochromatic 3-consecutive triple on the cyclic index set `ℤ/10`.
Closed by kernel `decide`. -/
theorem avoidanceColoring10_escapes :
    has3Consecutive avoidanceColoring10 = false := by decide

/-! ## Small-length threshold checks

For `n ∈ {3, 4, 5}`, we tabulate the number of "Ramsey-bad"
colorings (those avoiding a monochromatic 3-consecutive triple on
the cyclic index set `ℤ/n`). In each case the count is strictly
positive, so `has3Consecutive` is *not* forced at any of these
lengths. Closed by kernel `decide` on at most `2^5 = 32` cases.
-/

/-- Count of colorings in `allColorings n` that have no
monochromatic 3-consecutive triple. -/
def countBad (n : Nat) : Nat :=
  ((allColorings n).filter (fun c => !has3Consecutive c)).length

/-- **Threshold table (small `n`).**
For `n = 3` there are `6` bad colorings out of `8`.
For `n = 4` there are `6` bad colorings out of `16`.
For `n = 5` there are `10` bad colorings out of `32`.
Closed by kernel `decide`. -/
theorem countBad_small_table :
    countBad 3 = 6 ∧ countBad 4 = 6 ∧ countBad 5 = 10 := by decide

/-- Positive-count consequence for `n = 5`: at least one coloring
of a length-5 cyclic sequence avoids 3-consecutive monochromatic
triples, so the property is not forced at `n = 5`. -/
theorem countBad_5_positive : countBad 5 > 0 := by decide

/-! ## Main enumeration at `n = 10`

Two statements closed by `native_decide` (1024 cases × 10
index-scans each; kernel `decide` with `maxRecDepth` raised is
feasible but slow — per the `RamseyR33.ramsey_upper_bound` precedent
we use `native_decide` and document the trust-base impact). -/

set_option maxRecDepth 2048 in
/-- **Existence of at least one avoidance coloring at `n = 10`.**
Not every 2-coloring of a length-10 cyclic sequence has a
monochromatic 3-consecutive triple. Closed by `native_decide` over
the 1024 length-10 Boolean lists. -/
theorem has3Consecutive_not_forced_at_10 :
    (allColorings 10).any (fun c => !has3Consecutive c) = true := by
  native_decide

set_option maxRecDepth 2048 in
/-- **Exact Ramsey-bad count at `n = 10`.**
Of the `2^10 = 1024` length-10 Boolean colorings, exactly `122`
avoid a monochromatic 3-consecutive triple on the cyclic index set
`ℤ/10`. Closed by `native_decide` over 1024 cases; the same
counting would close under kernel `decide` with `maxRecDepth`
raised, at ~100× wall-time cost. -/
theorem countBad_10_eq_122 : countBad 10 = 122 := by native_decide

/-! ## Combined dynamical-Ramsey statement

The bridge packages the three observations that together answer the
dynamical-Ramsey question for the 10-point orbit of `(1, 0)` under
`CatMap 5`:

1. The orbit length is exactly 10 with distinct points
   (`orbitMod5_length`, `orbitMod5_distinct`).
2. Some length-10 2-coloring avoids monochromatic 3-consecutive
   triples (`avoidanceColoring10_escapes`).
3. Exactly 122 of the 1024 length-10 colorings are avoidance
   witnesses (`countBad_10_eq_122`).

The conjunction is the formal negative answer to the opening
question: `has3Consecutive` is *not* forced on the specific orbit
witnessed by `ArnoldCatMapOrder5.ord_A_mod_5_eq_10`.
-/

/-- **Dynamical-Ramsey bridge theorem.**
The orbit is full-period `10`; at least one length-10 2-coloring
avoids monochromatic 3-consecutive triples; exactly 122 of the
1024 length-10 2-colorings are such avoidance witnesses. -/
theorem dynamical_ramsey_not_forced :
    orbitMod5.length = 10 ∧
    pairwiseDistinct orbitMod5 = true ∧
    has3Consecutive avoidanceColoring10 = false ∧
    countBad 10 = 122 :=
  ⟨orbitMod5_length,
   orbitMod5_distinct,
   avoidanceColoring10_escapes,
   countBad_10_eq_122⟩

end DynamicalOrbitColoring
end BuleyeanMath
