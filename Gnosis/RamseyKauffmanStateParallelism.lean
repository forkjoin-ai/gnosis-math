import Init

/-!
# Ramsey/Kauffman State Parallelism — Shared Boolean Substrate

This module formalizes a *structural* parallelism between two superficially
unrelated combinatorial constructions:

* The `2^15` two-colorings of the edge set of `K_6` (Ramsey's theorem
  substrate).
* The `2^15` Kauffman-bracket state-sums on a hypothetical 15-crossing
  link diagram (each crossing independently receives an A- or B-smoothing).

Both instantiate a common schema we call `CompleteChoicePredicate n`: a
decidable Boolean filter on `List Bool` of length `n`. Ramsey realizes
the schema as a **universal** statement ("every choice satisfies the
predicate"), whereas the Kauffman bracket realizes it as a **sum**
("how many choices contribute to a given Laurent exponent?"). The
shared substrate is `2^n` length-`n` Boolean vectors; the `∀/Σ` duality
is then a pair of dual reductions of the same decidable filter.

## Honest scope

The bridge we prove is at the level of *schema*. We do **not** claim
that Ramsey bounds imply Kauffman identities, nor that the numerical
counts on the two sides agree (in general they do not). What we *do*
prove:

1. Both predicates are expressible as `List Bool → Bool`.
2. For a fixed length `n`, the count of satisfying vectors is
   decidable; moreover `(count satisfying) + (count failing) = 2^n`.
3. On `n = 15`, we compute *both* counts explicitly — the Ramsey
   count (number of `K_6` colorings forced to contain a monochromatic
   triangle) and a Kauffman-flavored count (number of 15-smoothing
   states with balanced A/B exponent) — witnessing schema-level
   parallelism without asserting numerical coincidence.

Zero `sorry`, no new `axiom`, `Init`-only. Scale-15 totals close under
`native_decide` with documentation; all smaller instances close under
kernel `decide`.
-/

namespace Gnosis
namespace RamseyKauffmanStateParallelism

/-! ## The shared schema: complete-choice Boolean predicates -/

/-- `CompleteChoicePredicate n` names a decidable Boolean filter on
length-`n` choice vectors. The `n` is a documentary parameter — the
predicate itself is just a function `List Bool → Bool`; we enforce
the length elsewhere via `List.length c = n`. -/
abbrev CompleteChoicePredicate (_n : Nat) := List Bool → Bool

/-- Enumerate every `List Bool` of length `n`. Produces `2^n` lists.
Kept local (rather than reused from Ramsey/Kauffman modules) to keep
this file `Init`-only with no cross-module import. -/
def allBoolVecs : (n : Nat) → List (List Bool)
  | 0 => [[]]
  | Nat.succ k =>
    let tails := allBoolVecs k
    (tails.map (fun t => false :: t)) ++ (tails.map (fun t => true :: t))

/-- Tail-recursive counter accumulator for `countSatisfying`. -/
def countSatisfyingAux (p : List Bool → Bool) :
    Nat → List (List Bool) → Nat
  | acc, [] => acc
  | acc, xs :: rest =>
    countSatisfyingAux p (acc + (if p xs then 1 else 0)) rest

/-- Count entries of a `List (List Bool)` that satisfy a Boolean
predicate. Tail-recursive so that `native_decide` on `2^15` inputs
does not exhaust the interpreter's call stack. -/
def countSatisfying (p : List Bool → Bool)
    (vs : List (List Bool)) : Nat :=
  countSatisfyingAux p 0 vs

/-- Tail-recursive accumulator for `countFailing`. -/
def countFailingAux (p : List Bool → Bool) :
    Nat → List (List Bool) → Nat
  | acc, [] => acc
  | acc, xs :: rest =>
    countFailingAux p (acc + (if p xs then 0 else 1)) rest

/-- Count entries that *fail* the predicate (the `∀`-obstruction
count). Tail-recursive dual to `countSatisfying`. -/
def countFailing (p : List Bool → Bool)
    (vs : List (List Bool)) : Nat :=
  countFailingAux p 0 vs

/-! ## Ramsey side — inlined `hasMonoTriangle` for `K_n`

We duplicate the edge-indexing, triangle enumeration, and
monochromatic-triangle detector from `RamseyR33.lean` rather than
importing it, to keep this module self-contained and `Init`-only. -/

/-- Indexed lookup on `List Bool` with `false` as the out-of-bounds
default. -/
def nthBool : List Bool → Nat → Bool
  | [], _ => false
  | x :: _, 0 => x
  | _ :: xs, Nat.succ k => nthBool xs k

/-- Linear index of the edge `{i, j}` in the upper-triangle
encoding of `K_n`, assuming `i < j < n`. -/
def edgeIndex (n i j : Nat) : Nat :=
  i * (2 * n - i - 1) / 2 + (j - i - 1)

/-- Read the color of edge `{i, j}` from a flat `List Bool` encoding. -/
def edgeColor (n : Nat) (c : List Bool) (i j : Nat) : Bool :=
  if i = j then false
  else
    let a := if i < j then i else j
    let b := if i < j then j else i
    let k := edgeIndex n a b
    nthBool c k

/-- All triples `(i, j, k)` with `0 ≤ i < j < k < n`. -/
def triples (n : Nat) : List (Nat × Nat × Nat) :=
  let is := List.range n
  is.foldr (fun i acc =>
    let js := List.range n
    js.foldr (fun j acc' =>
      if i < j then
        let ks := List.range n
        ks.foldr (fun k acc'' =>
          if j < k then (i, j, k) :: acc'' else acc'') acc'
      else acc') acc) []

/-- `true` iff the triangle `(i, j, k)` is monochromatic under `c`. -/
def triangleMono (n : Nat) (c : List Bool) (i j k : Nat) : Bool :=
  let x := edgeColor n c i j
  let y := edgeColor n c j k
  let z := edgeColor n c i k
  (x && y && z) || ((!x) && (!y) && (!z))

/-- `true` iff `c` contains at least one monochromatic triangle on `K_n`. -/
def hasMonoTriangle (n : Nat) (c : List Bool) : Bool :=
  (triples n).any (fun ijk => triangleMono n c ijk.1 ijk.2.1 ijk.2.2)

/-- **Ramsey-side realization of the schema.**
The `K_6`-monochromatic-triangle predicate viewed as a
`CompleteChoicePredicate 15`. -/
def ramseyPred : CompleteChoicePredicate 15 := hasMonoTriangle 6

/-! ## Kauffman side — state-weight filters on smoothings

A smoothing vector `s : List Bool` of length `n` assigns each of `n`
crossings an A-smoothing (`true`) or a B-smoothing (`false`). The
Kauffman state sum attaches the monomial `A^{a(s)-b(s)}` to each
state. We only need the integer exponent `a(s) - b(s)` here — not
the polynomial ring — because the question "how many states land at
a target exponent?" is decidable over the finite enumeration. -/

/-- Exponent contribution `a(s) - b(s)` of a state as an `Int`.
`true` smoothings add `+1`; `false` smoothings add `-1`. Matches
`stateExp` in `KauffmanBracketFinite.lean`. -/
def kauffmanStateWeight : List Bool → Int
  | [] => 0
  | true :: xs => 1 + kauffmanStateWeight xs
  | false :: xs => -1 + kauffmanStateWeight xs

/-- **Kauffman-side realization of the schema.**
Given a target Laurent exponent `target : Int`, the predicate
"this smoothing contributes to the coefficient at `A^target`"
is a `CompleteChoicePredicate n` for any `n`. -/
def kauffmanExponentTargetPred (target : Int) :
    CompleteChoicePredicate 15 :=
  fun s => decide (kauffmanStateWeight s = target)

/-- The bracket coefficient at a given Laurent exponent, *restricted
to the monomial exponent count* (i.e. ignoring `δ^{loops-1}` loop
factors). This counts states whose A-count minus B-count equals
`target`; it is the natural schema-level companion to
`ramseyPred`. -/
def bracketCoeffCount (n : Nat) (target : Int) : Nat :=
  countSatisfying (fun s => decide (kauffmanStateWeight s = target))
    (allBoolVecs n)

/-! ## Concrete duality instance at `n = 4`

We pick `n = 4` because the enumeration `2^4 = 16` is small enough
for `decide` to chew through easily, yet large enough to exhibit the
`∀/Σ` dual structure.

### Ramsey-flavored ∀ (falsified)

Define `ramseyFlavor c := decide (c.countMore3)` — the filter
"more than three `true`s". Over length-`4` vectors this predicate
fails the universal claim "every vector has at most three `true`s"
because `[true, true, true, true]` has four. We witness the failure
by exhibiting the unique counter-example. -/

/-- Count `true`-entries in a `List Bool`. Local copy to avoid
`List.count` API drift. -/
def countTrues : List Bool → Nat
  | [] => 0
  | true :: xs => 1 + countTrues xs
  | false :: xs => countTrues xs

/-- The Ramsey-flavored filter at `n = 4`: "more than three `true`s". -/
def ramseyFlavor4 : List Bool → Bool :=
  fun c => decide (countTrues c > 3)

/-- The unique witness: the all-`true` vector of length 4 satisfies
`ramseyFlavor4` (and is the only length-4 vector that does). -/
theorem ramseyFlavor4_witness :
    ramseyFlavor4 [true, true, true, true] = true := by decide

/-- The universal claim "every length-4 Boolean vector has at most
three `true`s" is *false* — exactly one vector violates it. -/
theorem ramseyFlavor4_universal_fails :
    (allBoolVecs 4).all (fun c => !(ramseyFlavor4 c)) = false := by decide

/-- The failure count equals `1`: only `[true, true, true, true]`
violates the bound. -/
theorem ramseyFlavor4_failure_count :
    countSatisfying ramseyFlavor4 (allBoolVecs 4) = 1 := by decide

/-! ### Kauffman-flavored Σ (exact count)

Among the `2^4 = 16` length-4 smoothings, those with `a(s) = b(s)`
(balanced A/B exponent, i.e. `kauffmanStateWeight s = 0`) are
exactly the `C(4,2) = 6` states with two A-smoothings and two
B-smoothings. -/

/-- Six balanced states at `n = 4`. -/
theorem kauffman_balanced_count_4 :
    countSatisfying
      (fun s => decide (kauffmanStateWeight s = (0 : Int)))
      (allBoolVecs 4) = 6 := by decide

/-! ## Bridge theorem: ∀/Σ partition of the `2^n` substrate

For any `CompleteChoicePredicate n` and any enumeration `vs`, the
satisfying and failing counts partition `|vs|`. Specialized to
`vs = allBoolVecs n`, this gives
`(count satisfying) + (count failing) = 2^n`,
which is the schema-level statement that the `∀` obstruction and
the `Σ` satisfaction count are dual reductions of the same filter. -/

/-- Accumulator lemma: the auxiliary satisfying-counter with
starting accumulator `k` equals `k` plus the count at accumulator
`0`. -/
theorem countSatisfyingAux_acc (p : List Bool → Bool) :
    ∀ (k : Nat) (vs : List (List Bool)),
      countSatisfyingAux p k vs = k + countSatisfyingAux p 0 vs
  | _, [] => by simp [countSatisfyingAux]
  | k, x :: rest => by
      simp only [countSatisfyingAux, Nat.zero_add]
      rw [countSatisfyingAux_acc p (k + (if p x then 1 else 0)) rest,
          countSatisfyingAux_acc p (if p x then 1 else 0) rest]
      exact Nat.add_assoc k (if p x then 1 else 0) (countSatisfyingAux p 0 rest)

/-- Accumulator lemma for `countFailingAux`. -/
theorem countFailingAux_acc (p : List Bool → Bool) :
    ∀ (k : Nat) (vs : List (List Bool)),
      countFailingAux p k vs = k + countFailingAux p 0 vs
  | _, [] => by simp [countFailingAux]
  | k, x :: rest => by
      simp only [countFailingAux, Nat.zero_add]
      rw [countFailingAux_acc p (k + (if p x then 0 else 1)) rest,
          countFailingAux_acc p (if p x then 0 else 1) rest]
      exact Nat.add_assoc k (if p x then 0 else 1) (countFailingAux p 0 rest)

theorem countSplit_generic (p : List Bool → Bool) :
    ∀ (vs : List (List Bool)),
      countSatisfying p vs + countFailing p vs = vs.length
  | [] => rfl
  | x :: rest => by
      have ih := countSplit_generic p rest
      unfold countSatisfying countFailing at *
      simp only [countSatisfyingAux, countFailingAux, List.length,
        Nat.zero_add]
      rw [countSatisfyingAux_acc p (if p x then 1 else 0) rest,
          countFailingAux_acc p (if p x then 0 else 1) rest]
      by_cases hpx : p x = true
      · -- p x = true: if-branches collapse to 1 and 0
        rw [if_pos hpx, if_pos hpx]
        -- Goal: 1 + countSatisfyingAux p 0 rest + (0 + countFailingAux p 0 rest) = rest.length + 1
        rw [Nat.zero_add, Nat.add_assoc 1 (countSatisfyingAux p 0 rest)
              (countFailingAux p 0 rest), ih, Nat.add_comm 1 rest.length]
      · have hfalse : p x = false := by cases hx : p x <;> simp_all
        have hpxNot : ¬ (p x = true) := hpx
        rw [if_neg hpxNot, if_neg hpxNot]
        -- Goal: 0 + countSatisfyingAux p 0 rest + (1 + countFailingAux p 0 rest) = rest.length + 1
        rw [Nat.zero_add,
            ← Nat.add_assoc (countSatisfyingAux p 0 rest) 1 (countFailingAux p 0 rest),
            Nat.add_comm (countSatisfyingAux p 0 rest) 1,
            Nat.add_assoc 1 (countSatisfyingAux p 0 rest) (countFailingAux p 0 rest), ih,
            Nat.add_comm 1 rest.length]

/-- `allBoolVecs n` has exactly `2^n` entries. Closed by `decide` at
`n = 4`. -/
theorem allBoolVecs_length_4 : (allBoolVecs 4).length = 16 := by decide

/-- **Concrete duality at `n = 4`.** For `ramseyFlavor4`, the
satisfying count is `1`, the failing count is `15`, and the sum is
`16 = 2^4`. This witnesses the `∀/Σ` dual reduction on a shared
Boolean substrate. -/
theorem ramsey_kauffman_duality_instance_4 :
    countSatisfying ramseyFlavor4 (allBoolVecs 4) = 1 ∧
    countFailing ramseyFlavor4 (allBoolVecs 4) = 15 ∧
    countSatisfying ramseyFlavor4 (allBoolVecs 4)
      + countFailing ramseyFlavor4 (allBoolVecs 4) = 16 := by decide

/-! ## Scale-15 witness: both predicates, both counts

We now compute the satisfying count for each side at the shared
scale `n = 15` — the scale at which the Ramsey parallelism "bites"
(`K_6` has 15 edges; a hypothetical 15-crossing diagram has 15
smoothings).

### Ramsey count at `n = 15`

The Ramsey upper bound `R(3,3) ≤ 6` is the statement that *every*
length-15 `K_6` coloring contains a monochromatic triangle, i.e.
`countSatisfying ramseyPred (allBoolVecs 15) = 32768` and
`countFailing ramseyPred (allBoolVecs 15) = 0`. The scale
`2^15 = 32768` has the same elaboration profile as in
`RamseyR33.lean`, so kernel `decide` runs past the tactic budget;
we close with `native_decide`, matching that file's strategy. The
underlying computation is pure, total, and decidable.

### Kauffman count at `n = 15`

The count of length-15 smoothings at the balanced exponent `0` is
*zero*: with an odd number of crossings, `a(s) - b(s)` has the
same parity as `n`, so it cannot equal `0` when `n = 15`. At
`target = 1`, the count is `C(15, 8) = 6435` (eight A-smoothings,
seven B-smoothings). We report both as `native_decide`-closed
scale-15 witnesses.

The two counts `32768` (Ramsey) and `6435` (Kauffman target=1)
differ, as expected — the schema sharing is the point, not the
numerical value. -/

/-- **Scale-15 Ramsey count (satisfying).**
All `2^15 = 32768` edge-colorings of `K_6` satisfy
`hasMonoTriangle 6`. Closed by `native_decide` per the Ramsey
file's `ramsey_upper_bound` strategy. -/
theorem ramsey_count_15_all :
    countSatisfying ramseyPred (allBoolVecs 15) = 32768 := by
  native_decide

/-- **Scale-15 Ramsey failure count.**
No length-15 coloring escapes — `countFailing = 0`. Dual to
`ramsey_count_15_all`. Closed by `native_decide`. -/
theorem ramsey_count_15_failing :
    countFailing ramseyPred (allBoolVecs 15) = 0 := by
  native_decide

/-- **Scale-15 Kauffman count at `target = 0`.**
Parity argument: with an odd number of crossings, no smoothing
state is balanced. Count is `0`. Closed by `native_decide` over
the full `2^15` enumeration (the parity argument is *not*
formalized; we rely on brute enumeration, matching the module's
"finite choice" spirit). -/
theorem kauffman_count_15_target0 :
    countSatisfying (kauffmanExponentTargetPred 0) (allBoolVecs 15) = 0 := by
  native_decide

/-- **Scale-15 Kauffman count at `target = 1`.**
Corresponds to `C(15, 8) = 6435` smoothings with eight A-type and
seven B-type choices. Closed by `native_decide`. -/
theorem kauffman_count_15_target1 :
    countSatisfying (kauffmanExponentTargetPred 1) (allBoolVecs 15) = 6435 := by
  native_decide

/-- **Honest schema-level witness.**
The Ramsey side forces every length-15 vector to satisfy its
predicate (`count = 32768`); a Kauffman-flavored predicate with
`target = 1` is satisfied by exactly `6435` vectors. The counts
differ — as they must, since the two predicates filter different
structure. The *bridge* is that both predicates inhabit the same
type `CompleteChoicePredicate 15` and both counts are recovered
by the same generic `countSatisfying`/`countFailing` partition.
That is, Ramsey and Kauffman-bracket state enumeration *instantiate*
a common `∀/Σ`-dual schema over `2^n` Boolean choices. -/
theorem schema_parallelism_15 :
    countSatisfying ramseyPred (allBoolVecs 15) = 32768 ∧
    countSatisfying (kauffmanExponentTargetPred 1) (allBoolVecs 15) = 6435 ∧
    -- partition identity at scale 15 for the Ramsey side:
    countSatisfying ramseyPred (allBoolVecs 15)
      + countFailing ramseyPred (allBoolVecs 15) = 32768 :=
  ⟨ramsey_count_15_all,
   kauffman_count_15_target1,
   by
     have := countSplit_generic ramseyPred (allBoolVecs 15)
     -- `(allBoolVecs 15).length = 32768` by native evaluation
     have hlen : (allBoolVecs 15).length = 32768 := by native_decide
     rw [hlen] at this
     exact this⟩

end RamseyKauffmanStateParallelism
end Gnosis
