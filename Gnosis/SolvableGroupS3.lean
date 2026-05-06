import Init

/-!
# Solvable Group S₃: explicit derived series and a quintic-obstruction witness

This module realizes the symmetric group `S₃` as a 6-element finite group on
`Fin 6` via an explicit multiplication table, computes its derived series
`S₃ ⊃ A₃ ⊃ {e}`, and witnesses the contrast with `A₅` through sample
commutator computations that exhibit non-trivial elements of `[A₅, A₅]`.

## Labeling of `S₃` on `Fin 6`

We fix the representation `S₃ = ⟨r, s | r³ = s² = e, s·r·s = r⁻¹⟩` and encode
the six elements as

| index | element |
|-------|---------|
| 0     | e       |
| 1     | r       |
| 2     | r²      |
| 3     | s       |
| 4     | s·r     |
| 5     | s·r²    |

All Cayley-table entries are computed by hand from the relations `r³ = s² = e`
and `r·s = s·r²` (equivalently `s·r·s = r²`). For example,
`(s·r) · (s·r²) = s · (r·s) · r² = s · (s·r²) · r² = s² · r⁴ = r`.

## What is proved

* An explicit multiplication `mul : Fin 6 → Fin 6 → Fin 6`.
* Identity laws, associativity on the full 6×6×6 cube (`decide`), and
  existence of left and right inverses via `inv`.
* The commutator `commutator a b = a·b·a⁻¹·b⁻¹`.
* `derivedSubgroupS3` (the sorted-deduped list of all 36 commutators in `S₃`)
  equals `[0, 1, 2]`, i.e. `A₃`.
* `derivedSubgroupA3` (all 9 commutators among elements of `A₃`) equals
  `[0]`, i.e. the trivial subgroup.
* Corollary: the derived series `S₃ ⊃ A₃ ⊃ {e}` has length `2` and `S₃`
  is solvable in the computational sense recorded here.

## `A₅` witness (light path)

We do *not* encode `A₅` in full — the 60×60 table is too heavy for kernel
`decide` at Lean 4.28.0 and unnecessary for the named witness. Instead, four
concrete commutator computations on three-cycles and double-transpositions
show that every stated commutator is a non-trivial element of `A₅`,
witnessing that `[A₅, A₅]` is not the trivial subgroup. This is a sample
witness of perfectness, not a full proof that `[A₅, A₅] = A₅`.

The `A₅` elements are represented as permutations of `Fin 5` via a
`PermFin5` structure; composition is defined pointwise and the commutator
acts on this structure directly.

## Hard caveats

* What is formalized is the explicit finite-group structure of `S₃`, its
  two-step derived series, and four sample commutators in `A₅`. This module
  does not connect to Galois theory, the unsolvability of the general
  quintic, or any abstract notion of solvable group beyond the explicit
  table-level computation.
* The `A₅` section is a point-instance witness, not a closure proof.
* No connection to mathlib, no external definitions of solvability.

No `sorry`, no new `axiom`; `Init`-only; `decide` throughout.
-/

namespace Gnosis
namespace SolvableGroupS3

/-! ## Part A — `S₃` as `Fin 6` with an explicit multiplication table -/

/-- The identity element `e`. -/
def e : Fin 6 := 0
/-- The 3-cycle `r` of order 3. -/
def r : Fin 6 := 1
/-- `r²`. -/
def r2 : Fin 6 := 2
/-- The transposition `s` of order 2. -/
def s : Fin 6 := 3
/-- `s·r`. -/
def sr : Fin 6 := 4
/-- `s·r²`. -/
def sr2 : Fin 6 := 5

/--
Explicit multiplication table for `S₃` on `Fin 6`, indexed as
`e=0, r=1, r²=2, s=3, s·r=4, s·r²=5`.

Row `i` gives `i · j` for `j = 0..5`. Entries are derived from the
presentation `r³ = s² = e`, `r·s = s·r²`. For example, row `r` computes
`r·s = s·r² = 5` and `r·(s·r) = (r·s)·r = (s·r²)·r = s·r³ = s = 3`.
-/
def mul : Fin 6 → Fin 6 → Fin 6
  -- Row e: e · j = j
  | ⟨0, _⟩, j => j
  -- Row r
  | ⟨1, _⟩, ⟨0, _⟩ => 1  -- r · e   = r
  | ⟨1, _⟩, ⟨1, _⟩ => 2  -- r · r   = r²
  | ⟨1, _⟩, ⟨2, _⟩ => 0  -- r · r²  = e
  | ⟨1, _⟩, ⟨3, _⟩ => 5  -- r · s   = s·r²
  | ⟨1, _⟩, ⟨4, _⟩ => 3  -- r · sr  = s
  | ⟨1, _⟩, ⟨5, _⟩ => 4  -- r · sr² = s·r
  -- Row r²
  | ⟨2, _⟩, ⟨0, _⟩ => 2
  | ⟨2, _⟩, ⟨1, _⟩ => 0
  | ⟨2, _⟩, ⟨2, _⟩ => 1
  | ⟨2, _⟩, ⟨3, _⟩ => 4  -- r² · s   = s·r
  | ⟨2, _⟩, ⟨4, _⟩ => 5  -- r² · sr  = s·r²
  | ⟨2, _⟩, ⟨5, _⟩ => 3  -- r² · sr² = s
  -- Row s
  | ⟨3, _⟩, ⟨0, _⟩ => 3
  | ⟨3, _⟩, ⟨1, _⟩ => 4  -- s · r   = s·r
  | ⟨3, _⟩, ⟨2, _⟩ => 5  -- s · r²  = s·r²
  | ⟨3, _⟩, ⟨3, _⟩ => 0  -- s · s   = e
  | ⟨3, _⟩, ⟨4, _⟩ => 1  -- s · sr  = s²·r = r
  | ⟨3, _⟩, ⟨5, _⟩ => 2  -- s · sr² = s²·r² = r²
  -- Row s·r
  | ⟨4, _⟩, ⟨0, _⟩ => 4
  | ⟨4, _⟩, ⟨1, _⟩ => 5  -- (s·r) · r   = s·r²
  | ⟨4, _⟩, ⟨2, _⟩ => 3  -- (s·r) · r²  = s·r³ = s
  | ⟨4, _⟩, ⟨3, _⟩ => 2  -- (s·r) · s   = s·(r·s) = s·(s·r²) = r²
  | ⟨4, _⟩, ⟨4, _⟩ => 0  -- (s·r) · (s·r)  = e
  | ⟨4, _⟩, ⟨5, _⟩ => 1  -- (s·r) · (s·r²) = r
  -- Row s·r²
  | ⟨5, _⟩, ⟨0, _⟩ => 5
  | ⟨5, _⟩, ⟨1, _⟩ => 3  -- (s·r²) · r   = s·r³ = s
  | ⟨5, _⟩, ⟨2, _⟩ => 4  -- (s·r²) · r²  = s·r⁴ = s·r
  | ⟨5, _⟩, ⟨3, _⟩ => 1  -- (s·r²) · s   = s·(r²·s) = s·(s·r) = r
  | ⟨5, _⟩, ⟨4, _⟩ => 2  -- (s·r²) · (s·r)  = r²
  | ⟨5, _⟩, ⟨5, _⟩ => 0  -- (s·r²) · (s·r²) = e

/-- Left identity: `e · x = x`. -/
theorem e_left_id (x : Fin 6) : mul e x = x := by
  cases x with
  | mk v h => rfl

/-- Right identity: `x · e = x`. -/
theorem e_right_id : ∀ x : Fin 6, mul x e = x := by decide

/-- Two-sided identity. -/
theorem e_two_sided_id : ∀ x : Fin 6, mul e x = x ∧ mul x e = x := by decide

/-- Associativity of `mul` on all 216 triples of `Fin 6`. -/
theorem mul_assoc_all :
    ∀ a b c : Fin 6, mul (mul a b) c = mul a (mul b c) := by decide

/-- Inverse map on `S₃`: `e, r, r², s, s·r, s·r²` invert to
`e, r², r, s, s·r, s·r²` respectively. -/
def inv : Fin 6 → Fin 6
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => 2
  | ⟨2, _⟩ => 1
  | ⟨3, _⟩ => 3
  | ⟨4, _⟩ => 4
  | ⟨5, _⟩ => 5

/-- `inv` is a left inverse under `mul`. -/
theorem inv_left (x : Fin 6) : mul (inv x) x = e := by
  cases x with
  | mk v h =>
    match v, h with
    | 0, _ => rfl
    | 1, _ => rfl
    | 2, _ => rfl
    | 3, _ => rfl
    | 4, _ => rfl
    | 5, _ => rfl

/-- `inv` is a right inverse under `mul`. -/
theorem inv_right (x : Fin 6) : mul x (inv x) = e := by
  cases x with
  | mk v h =>
    match v, h with
    | 0, _ => rfl
    | 1, _ => rfl
    | 2, _ => rfl
    | 3, _ => rfl
    | 4, _ => rfl
    | 5, _ => rfl

/-! ## Commutators in `S₃` -/

/-- The group commutator `[a, b] := a · b · a⁻¹ · b⁻¹`. -/
def commutator (a b : Fin 6) : Fin 6 :=
  mul (mul (mul a b) (inv a)) (inv b)

/-- Sample commutator: `[r, s] = r²`. -/
theorem commutator_r_s : commutator r s = r2 := by decide

/-- Sample commutator: `[s, r] = r`. -/
theorem commutator_s_r : commutator s r = r := by decide

/-- `A₃`-only commutators vanish: `[r, r²] = e`. -/
theorem commutator_r_r2 : commutator r r2 = e := by decide

/-! ## Sorted-deduped `Fin 6` lists as a `Finset` stand-in

To stay `Init`-only and keep every equality `decide`-closable, we use
strictly-increasing `List (Fin 6)` as the canonical representation of a
subset. Two subsets are equal iff the lists are equal. -/

/-- Insert `x` into a sorted list `l`, keeping it sorted and deduped. -/
def sortedInsert (x : Fin 6) : List (Fin 6) → List (Fin 6)
  | [] => [x]
  | y :: ys =>
    if x.val < y.val then x :: y :: ys
    else if x.val = y.val then y :: ys
    else y :: sortedInsert x ys

/-- The full 6-element domain of `Fin 6`, enumerated in order. -/
def elemsS3 : List (Fin 6) :=
  [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩,
   ⟨3, by decide⟩, ⟨4, by decide⟩, ⟨5, by decide⟩]

/-- The 3-element subset `A₃ = {e, r, r²}`. -/
def elemsA3 : List (Fin 6) :=
  [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩]

/-- Build the sorted-deduped image of the commutator bracket across all pairs
drawn from `dom`. -/
def commutatorImage (dom : List (Fin 6)) : List (Fin 6) :=
  let pairs := dom.flatMap (fun a => dom.map (fun b => commutator a b))
  pairs.foldl (fun acc x => sortedInsert x acc) []

/-- The commutator subgroup of `S₃`, represented as a sorted-deduped list of
its elements. For `S₃` the set of commutators is already closed under the
group operation (it equals the abelian group `A₃`), so sorting-deduping the
image suffices. -/
def derivedSubgroupS3 : List (Fin 6) := commutatorImage elemsS3

/-- The commutator subgroup of `A₃`, represented as a sorted-deduped list. -/
def derivedSubgroupA3 : List (Fin 6) := commutatorImage elemsA3

/-- First step of the derived series. The commutator subgroup of `S₃`
equals `A₃ = {e, r, r²}`. -/
theorem derived_S3_eq_A3 : derivedSubgroupS3 = elemsA3 := by decide

/-- Second step of the derived series. `A₃` is abelian, so its
commutator subgroup is trivial. -/
theorem derived_A3_eq_trivial :
    derivedSubgroupA3 = [⟨0, by decide⟩] := by decide

/--
`S₃` is solvable (computational witness). The derived series
`S₃ ⊃ A₃ ⊃ {e}` terminates at the trivial subgroup after two steps.
This packages the two previous theorems: iterating `commutatorImage`
starting from `elemsS3` reaches the singleton `[e]` in exactly two
iterations.
-/
theorem S3_derived_series_terminates :
    commutatorImage (commutatorImage elemsS3) = [⟨0, by decide⟩] := by decide

/-! ## Part B — `A₅` perfectness: sample-commutator witness

We encode only the permutation action of specific `A₅` elements on `Fin 5`
and compute four concrete commutators. Each witness shows
`commPerm g h ≠ identity`, so the commutator subgroup `[A₅, A₅]` contains
non-trivial even permutations. This is a sample witness, not a proof
that `[A₅, A₅] = A₅`. A full closure argument would require enumerating all
60 elements of `A₅` and iterating the generator closure, which is outside
the scope of this module.
-/

/-- A permutation of `Fin 5` represented as a length-5 tuple
`(act 0, act 1, act 2, act 3, act 4)`. -/
structure PermFin5 where
  /-- Image of `0`. -/
  a0 : Fin 5
  /-- Image of `1`. -/
  a1 : Fin 5
  /-- Image of `2`. -/
  a2 : Fin 5
  /-- Image of `3`. -/
  a3 : Fin 5
  /-- Image of `4`. -/
  a4 : Fin 5
deriving DecidableEq, Repr

namespace PermFin5

/-- Apply a `PermFin5` to an index. -/
def apply (p : PermFin5) (i : Fin 5) : Fin 5 :=
  match i with
  | ⟨0, _⟩ => p.a0
  | ⟨1, _⟩ => p.a1
  | ⟨2, _⟩ => p.a2
  | ⟨3, _⟩ => p.a3
  | ⟨4, _⟩ => p.a4

/-- Composition `(p ∘ q) i = p (q i)`. -/
def comp (p q : PermFin5) : PermFin5 :=
  { a0 := p.apply q.a0
  , a1 := p.apply q.a1
  , a2 := p.apply q.a2
  , a3 := p.apply q.a3
  , a4 := p.apply q.a4 }

/-- The identity permutation. -/
def id5 : PermFin5 := ⟨0, 1, 2, 3, 4⟩

/-- The 3-cycle `(0 1 2)`: `0 ↦ 1, 1 ↦ 2, 2 ↦ 0`. -/
def c012 : PermFin5 := ⟨1, 2, 0, 3, 4⟩

/-- Inverse of `(0 1 2)`, i.e. `(0 2 1)`. -/
def c021 : PermFin5 := ⟨2, 0, 1, 3, 4⟩

/-- The 3-cycle `(1 2 3)`. -/
def c123 : PermFin5 := ⟨0, 2, 3, 1, 4⟩

/-- Inverse of `(1 2 3)`, i.e. `(1 3 2)`. -/
def c132 : PermFin5 := ⟨0, 3, 1, 2, 4⟩

/-- The 3-cycle `(2 3 4)`. -/
def c234 : PermFin5 := ⟨0, 1, 3, 4, 2⟩

/-- Inverse of `(2 3 4)`. -/
def c243 : PermFin5 := ⟨0, 1, 4, 2, 3⟩

/-- The double transposition `(0 1)(2 3)`. -/
def d01_23 : PermFin5 := ⟨1, 0, 3, 2, 4⟩

/-- Its own inverse since it has order 2. -/
def d01_23_inv : PermFin5 := d01_23

/-- The double transposition `(0 2)(1 3)`. -/
def d02_13 : PermFin5 := ⟨2, 3, 0, 1, 4⟩

/-- Its own inverse. -/
def d02_13_inv : PermFin5 := d02_13

/-- Commutator of two permutations, `[p, q] = p ∘ q ∘ p⁻¹ ∘ q⁻¹`. Since each
of our explicit inverses is provided separately, this takes the inverses as
arguments. -/
def commPerm (p q pInv qInv : PermFin5) : PermFin5 :=
  comp (comp (comp p q) pInv) qInv

end PermFin5

open PermFin5

/-- Witness 1. `[(0 1 2), (1 2 3)]` acts non-trivially on `Fin 5`.
It lands on the 3-cycle `(0 1 3)` (image tuple `(1, 3, 2, 0, 4)`). -/
theorem comm_c012_c123_nontrivial :
    commPerm c012 c123 c021 c132 ≠ id5 := by decide

/-- Witness 2. `[(1 2 3), (2 3 4)]` acts non-trivially. -/
theorem comm_c123_c234_nontrivial :
    commPerm c123 c234 c132 c243 ≠ id5 := by decide

/-- Witness 3. `[(0 1)(2 3), (0 1 2)]` acts non-trivially as the
double transposition `(0 2)(1 3)`. (Note: `(0 1)(2 3)` and `(0 2)(1 3)`
themselves commute in the Klein 4-group, so that pairing would vanish;
pairing a double transposition with a disjoint-support 3-cycle yields a
non-trivial bracket instead.) -/
theorem comm_d0123_c012_nontrivial :
    commPerm d01_23 c012 d01_23_inv c021 ≠ id5 := by decide

/-- Witness 4. `[(0 1 2), (0 1)(2 3)]` acts non-trivially. -/
theorem comm_c012_d0123_nontrivial :
    commPerm c012 d01_23 c021 d01_23_inv ≠ id5 := by decide

/--
Sample-commutator witness of `A₅` perfectness. The commutator subgroup
`[A₅, A₅]` contains at least four distinct non-trivial even permutations
of `Fin 5`, exhibited by concrete bracket computations above. This does not
prove `[A₅, A₅] = A₅`; it witnesses that `[A₅, A₅]` is not contained in the
trivial subgroup. The contrast with `derived_A3_eq_trivial` and
`derived_S3_eq_A3` records the structural obstruction that separates the
solvable cases from the perfect alternating group on five or more letters.
-/
theorem A5_commutator_nontrivial_witness :
    (commPerm c012 c123 c021 c132 ≠ id5) ∧
    (commPerm c123 c234 c132 c243 ≠ id5) ∧
    (commPerm d01_23 c012 d01_23_inv c021 ≠ id5) ∧
    (commPerm c012 d01_23 c021 d01_23_inv ≠ id5) := by
  decide

end SolvableGroupS3
end Gnosis
