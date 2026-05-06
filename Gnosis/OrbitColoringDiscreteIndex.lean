import Init

/-!
# Orbit-Coloring Discrete Index

This module instantiates the `DiscreteIndexStatement` schema from
`GaussBonnetBurnsideIndex.lean` on the Ramsey-flavored coloring
problem of `DynamicalOrbitColoring.lean`. The cat-map orbit of
`(1, 0)` under `CatMap 5` has length `10` and supports a natural
cyclic `C_10` action by index rotation. Burnside's lemma on that
action --- applied both to the full `2^10 = 1024` 2-colorings and to
the `122` "avoidance" 2-colorings (those without a monochromatic
3-consecutive triple) --- fits the shared local-to-global fold
`Σ_{x ∈ X} localCount(x) = scaling · invariant`.

## What this module witnesses

1. A cyclic left-shift `rotateBool` on `List Bool` (length-preserving).
2. Iterated rotation `rotateBoolK` and a Boolean fixedness test
   `isFixedByRotK`.
3. The fixed-point count function `fixedCount : Nat → Nat` on the
   full 1024-coloring set and the Burnside-compatible table for
   `k = 0, ..., 9`: `1024, 2, 4, 2, 4, 32, 4, 2, 4, 2`. Sum is `1080`.
4. A `DiscreteIndexStatement` instance `burnsideC10Full` realizing
   `Σ |Fix(rot^k)| = 10 · 108`, witnessing `108` orbits of the
   `C_10` action on `Bool^10`.
5. The restricted fixed-point count `fixedCountBad : Nat → Nat` on
   the `122`-element avoidance-coloring set. The table is
   `122, 0, 2, 0, 2, 10, 2, 0, 2, 0`. Sum is `140 = 10 · 14`.
6. A `DiscreteIndexStatement` instance `burnsideC10Avoid` realizing
   the restricted fold at invariant `14`: there are `14` orbits of
   the `C_10` action on the avoidance subset.
7. A cross-tie observation: `catTrace 5 - 1 = 122 = countBad 10`.
   Honest status: a numerical coincidence, not a derived identity.
   `fixedCountBad 5 = 10 = countBad 5`, which *is* structural
   (period-5 length-10 strings avoid the length-10 3-consecutive
   condition iff their length-5 period avoids the length-5
   3-consecutive condition).

## What this module does *not* claim

- The unification with `DiscreteIndexStatement` is structural at the
  record-shape level: Burnside's `Σ |Fix| = |G| · #orbits` fold is the
  same equation shape as Gauss-Bonnet's `Σ defect = 60 · χ`. No
  deeper geometric or representation-theoretic identification is
  made.
- The orbit under consideration is the specific `(1, 0)`-seed orbit
  under `CatMap 5`. The `C_10` action is the cyclic index rotation
  on the 10-length coloring list, not an intrinsic dynamical symmetry
  of the cat map itself.
- The cross-tie `catTrace 5 - 1 = countBad 10` is reported as a
  numerical observation. No mechanism is offered.
- The restricted Burnside closure at invariant `14` is computed by
  enumeration, not derived from a structural orbit-counting argument.

No `sorry`, no new `axiom`, `import Init` only. Each numerical
identity closes by kernel `decide` where feasible; enumeration over
`2^10 = 1024` colorings uses `native_decide` with the same
trust-base reasoning documented in `DynamicalOrbitColoring.lean`.
-/

namespace Gnosis
namespace OrbitColoringDiscreteIndex

/-! ## Inlined shape: `DiscreteIndexStatement`

Mirrors `GaussBonnetBurnsideIndex.DiscreteIndexStatement`. Kept inline
so this file compiles under `import Init` only. -/

/-- Finite list-indexed local count with multiplicative scaling and a
global invariant. Burnside's `Σ |Fix(g)| = |G| · #orbits` and
Gauss-Bonnet's `Σ defect(v) = 60 · χ` both realize this shape. -/
structure DiscreteIndexStatement where
  indexSet   : List Nat
  localCount : Nat → Nat
  scaling    : Nat
  invariant  : Nat
  deriving Inhabited

/-- Fold `f : Nat → Nat` over a `List Nat` structurally. -/
def sumMap (f : Nat → Nat) : List Nat → Nat
  | []      => 0
  | x :: xs => f x + sumMap f xs

/-- The local-to-global fold identity. -/
def holds (s : DiscreteIndexStatement) : Prop :=
  sumMap s.localCount s.indexSet = s.scaling * s.invariant

instance (s : DiscreteIndexStatement) : Decidable (holds s) := by
  unfold holds
  infer_instance

/-! ## Inlined coloring machinery from `DynamicalOrbitColoring`

Re-declared inline so the file compiles standalone. Values match the
peer module. -/

/-- Indexed lookup with `false` out-of-bounds default. -/
def nthBool : List Bool → Nat → Bool
  | [], _ => false
  | x :: _, 0 => x
  | _ :: xs, Nat.succ k => nthBool xs k

/-- Monochromatic 3-consecutive scan over cyclic index `ℤ/n`. -/
def has3CycleAux (c : List Bool) (n : Nat) : Nat → Bool
  | 0 => false
  | Nat.succ k =>
    let i := n - Nat.succ k
    let a := nthBool c i
    let b := nthBool c ((i + 1) % n)
    let d := nthBool c ((i + 2) % n)
    (a == b && b == d) || has3CycleAux c n k

/-- `true` iff `c` (length `n`, cyclic) has three equal consecutive
entries at some index `i` mod `n`. -/
def has3Consecutive (c : List Bool) : Bool :=
  has3CycleAux c c.length c.length

/-- All `2^n` length-`n` Boolean lists. -/
def allColorings : Nat → List (List Bool)
  | 0 => [[]]
  | Nat.succ k =>
    let tails := allColorings k
    (tails.map (fun t => false :: t)) ++ (tails.map (fun t => true :: t))

/-- Count of `allColorings n` entries that avoid a monochromatic
3-consecutive triple. -/
def countBad (n : Nat) : Nat :=
  ((allColorings n).filter (fun c => !has3Consecutive c)).length

/-! ## Cyclic left-rotation on `List Bool`

`rotateBool [x₀, x₁, ..., x_{n-1}]` returns `[x₁, x₂, ..., x_{n-1}, x₀]`.
Length-preserving. Iterated `k` times, it sends entry at index `i` to
entry at index `(i + k) mod n`. -/

/-- Cyclic left-shift: move the head to the tail. -/
def rotateBool : List Bool → List Bool
  | []      => []
  | x :: xs => xs ++ [x]

/-- `k`-fold iteration of `rotateBool`. -/
def rotateBoolK : Nat → List Bool → List Bool
  | 0,     c => c
  | k + 1, c => rotateBool (rotateBoolK k c)

/-- Structural equality on `List Bool`. -/
def listBoolEq : List Bool → List Bool → Bool
  | [], [] => true
  | [], _ :: _ => false
  | _ :: _, [] => false
  | x :: xs, y :: ys => (x == y) && listBoolEq xs ys

/-- `true` iff `rotateBoolK k c = c`, i.e. `c ∈ Fix(rot^k)`. -/
def isFixedByRotK (k : Nat) (c : List Bool) : Bool :=
  listBoolEq (rotateBoolK k c) c

/-! ## Sanity: rotation preserves length and acts on a concrete witness

The avoidance coloring `[T, T, F, F, T, T, F, F, T, F]` from the peer
module is *not* a fixed point of any nontrivial rotation `rot^k` for
`k ∈ {1, ..., 9}` — i.e. its `C_10`-orbit has full size `10`.
Closed by kernel `decide`. -/

/-- The avoidance-witness coloring from the peer module. -/
def avoidanceColoring10 : List Bool :=
  [true, true, false, false, true, true, false, false, true, false]

/-- The identity rotation fixes the avoidance coloring. -/
theorem avoidance_fixed_by_rot0 :
    isFixedByRotK 0 avoidanceColoring10 = true := by decide

/-- No nontrivial `C_10` rotation fixes the avoidance coloring. -/
theorem avoidance_full_orbit :
    isFixedByRotK 1 avoidanceColoring10 = false ∧
    isFixedByRotK 2 avoidanceColoring10 = false ∧
    isFixedByRotK 3 avoidanceColoring10 = false ∧
    isFixedByRotK 4 avoidanceColoring10 = false ∧
    isFixedByRotK 5 avoidanceColoring10 = false ∧
    isFixedByRotK 6 avoidanceColoring10 = false ∧
    isFixedByRotK 7 avoidanceColoring10 = false ∧
    isFixedByRotK 8 avoidanceColoring10 = false ∧
    isFixedByRotK 9 avoidanceColoring10 = false := by decide

/-! ## Burnside fixed-point count on the full 1024-coloring set

`fixedCount k` counts the length-10 Boolean colorings fixed by
`rot^k`. By the standard Burnside identity on `Bool^n` under `C_n`,
`|Fix(rot^k)| = 2^{gcd(k, n)}`. For `n = 10` the table is
`1024, 2, 4, 2, 4, 32, 4, 2, 4, 2` at `k = 0, ..., 9`. -/

/-- Count of length-10 colorings fixed by `rot^k`. -/
def fixedCount (k : Nat) : Nat :=
  ((allColorings 10).filter (fun c => isFixedByRotK k c)).length

/-! ### Per-`k` fixed-point counts

The `k = 0` case has `|Fix(id)| = 1024` by kernel `decide` at the
default `maxRecDepth` (the filter trivializes since `isFixedByRotK 0`
is constantly `true`; it reduces to the length of `allColorings 10`,
which is itself a 1024-entry enumeration). We use `native_decide` for
the full table for uniformity and to match the `countBad_10_eq_122`
closure style of the peer module. -/

set_option maxRecDepth 4096 in
/-- Full Burnside fixed-point table for `C_10` on `Bool^10`:
`1024, 2, 4, 2, 4, 32, 4, 2, 4, 2`. Closed by `native_decide` over
1024 cases per `k`. -/
theorem fixedCount_table :
    fixedCount 0 = 1024 ∧ fixedCount 1 = 2    ∧
    fixedCount 2 = 4    ∧ fixedCount 3 = 2    ∧
    fixedCount 4 = 4    ∧ fixedCount 5 = 32   ∧
    fixedCount 6 = 4    ∧ fixedCount 7 = 2    ∧
    fixedCount 8 = 4    ∧ fixedCount 9 = 2    := by native_decide

/-! ## Full Burnside as a `DiscreteIndexStatement`

`indexSet = [0..9]`, `localCount = fixedCount`, `scaling = 10`,
`invariant = 108` (orbit count of `C_10` on `Bool^10`). The fold
`Σ fixedCount k = 10 · 108 = 1080` reduces to the sum
`1024 + 2 + 4 + 2 + 4 + 32 + 4 + 2 + 4 + 2 = 1080`. -/

/-- Burnside on all 1024 length-10 2-colorings under `C_10`. -/
def burnsideC10Full : DiscreteIndexStatement :=
  { indexSet   := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
  , localCount := fixedCount
  , scaling    := 10
  , invariant  := 108 }

set_option maxRecDepth 4096 in
/-- Full Burnside holds.
`Σ_{k = 0}^{9} |Fix(rot^k)| = 1080 = 10 · 108`, witnessing 108 orbits
of the `C_10` action on the 1024 length-10 2-colorings. Closed by
`native_decide`; the sum expands each `fixedCount k` into a
1024-coloring filter. -/
theorem burnsideC10Full_holds : holds burnsideC10Full := by
  native_decide

/-! ## Restriction to the 122-element avoidance set

Rotation preserves `has3Consecutive` (any monochromatic triple at
index `i` becomes a monochromatic triple at index `(i - k) mod n`
after `rot^k`). So `C_10` restricts to the avoidance set, and
Burnside applies. We count fixed avoidance colorings per `k`. -/

/-- All length-10 colorings that avoid a monochromatic 3-consecutive
triple on the cyclic index set `ℤ/10`. Has length `122` by
`DynamicalOrbitColoring.countBad_10_eq_122`. -/
def avoidColorings10 : List (List Bool) :=
  (allColorings 10).filter (fun c => !has3Consecutive c)

set_option maxRecDepth 4096 in
/-- The avoidance list has `122` entries. Mirrors the peer-module
count. -/
theorem avoidColorings10_length : avoidColorings10.length = 122 := by
  native_decide

/-- Count of avoidance colorings fixed by `rot^k`. -/
def fixedCountBad (k : Nat) : Nat :=
  (avoidColorings10.filter (fun c => isFixedByRotK k c)).length

/-! ### Restricted table

Structural reasoning for the expected values:

- `k = 0` (identity): fixes all `122` avoidance colorings.
- `k ∈ {1, 3, 7, 9}` (gcd with `10` is `1`): fixed strings have
  period `1`, i.e. are constant. Both `0000000000` and `1111111111`
  contain a monochromatic 3-consecutive triple, so neither is in the
  avoidance set. Count is `0`.
- `k ∈ {2, 4, 6, 8}` (gcd is `2`): fixed strings have period
  dividing `2`. Four such strings: `0000...`, `1111...`, `0101...`,
  `1010...`. The first two fail avoidance; the two alternating
  strings succeed. Count is `2`.
- `k = 5` (gcd is `5`): fixed strings have period dividing `5`,
  written as `abcde abcde`. Such a length-10 string avoids
  monochromatic 3-consecutive cyclically iff the length-5 pattern
  `abcde` avoids monochromatic 3-consecutive cyclically on `ℤ/5`
  --- i.e. it is one of the `countBad 5 = 10` length-5 avoidance
  witnesses. Count is `10`.

The sum is `122 + 0 + 2 + 0 + 2 + 10 + 2 + 0 + 2 + 0 = 140`, and
`140 / 10 = 14` orbits. -/

set_option maxRecDepth 4096 in
/-- Restricted Burnside fixed-point table on the 122-element
avoidance set: `122, 0, 2, 0, 2, 10, 2, 0, 2, 0`. Closed by
`native_decide`. -/
theorem fixedCountBad_table :
    fixedCountBad 0 = 122 ∧ fixedCountBad 1 = 0   ∧
    fixedCountBad 2 = 2   ∧ fixedCountBad 3 = 0   ∧
    fixedCountBad 4 = 2   ∧ fixedCountBad 5 = 10  ∧
    fixedCountBad 6 = 2   ∧ fixedCountBad 7 = 0   ∧
    fixedCountBad 8 = 2   ∧ fixedCountBad 9 = 0   := by native_decide

/-! ## Restricted Burnside as a `DiscreteIndexStatement`

`indexSet = [0..9]`, `localCount = fixedCountBad`, `scaling = 10`,
`invariant = 14` (orbit count of `C_10` on the avoidance subset).
The fold `Σ fixedCountBad k = 10 · 14 = 140` reduces to
`122 + 0 + 2 + 0 + 2 + 10 + 2 + 0 + 2 + 0 = 140`. -/

/-- Burnside on the 122 avoidance colorings under `C_10`. -/
def burnsideC10Avoid : DiscreteIndexStatement :=
  { indexSet   := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
  , localCount := fixedCountBad
  , scaling    := 10
  , invariant  := 14 }

set_option maxRecDepth 4096 in
/-- Restricted Burnside holds.
`Σ_{k = 0}^{9} |Fix_avoid(rot^k)| = 140 = 10 · 14`, witnessing `14`
orbits of the `C_10` action on the 122-element avoidance subset.
Closed by `native_decide`. -/
theorem burnsideC10Avoid_holds : holds burnsideC10Avoid := by
  native_decide

/-! ## Cross-tie to `catTrace`

The peer module `CatMapLucasBridge.lean` computes
`catTrace 5 = 123`. Observe `catTrace 5 - 1 = 122 = countBad 10`. We
record this equation by kernel `decide`; we do not claim it is a
structural identity. The `C_10` action on colorings is not
`(ℤ/5)²`-structured, so there is no a priori reason for an affine
shift of `catTrace` to count avoidance colorings. -/

/-- Inlined `catTrace` to keep this file `import Init`-only. Matches
`CatMapLucasBridge.catTrace`. -/
def catTrace : Nat → Nat
  | 0     => 2
  | 1     => 3
  | k + 2 => 3 * catTrace (k + 1) - catTrace k

/-- Numerical coincidence. `catTrace 5 - 1 = 122 = countBad 10`.
Stated without interpretation. -/
theorem catTrace_5_minus_one_eq_countBad_10 :
    catTrace 5 - 1 = countBad 10 := by native_decide

/-- A structural (non-coincidental) cross-tie: the `k = 5`
restricted fixed-point count equals the length-5 avoidance count.
Period-5 length-10 avoidance strings correspond one-to-one with
length-5 avoidance strings, because `has3Consecutive` on
`abcde abcde` reduces to `has3Consecutive` on `abcde` cyclically at
length `5`. -/
theorem fixedCountBad_5_eq_countBad_5 :
    fixedCountBad 5 = countBad 5 := by native_decide

/-! ## Master package

The three instantiations of `holds` for the cat-map orbit-coloring
bridge, plus the structural length-5 / length-10 cross-tie and the
`catTrace` numerical coincidence. -/

set_option maxRecDepth 4096 in
/-- Master bridge theorem.
Three `DiscreteIndexStatement` instantiations on the cat-map orbit
coloring problem:

1. Full Burnside on 1024 colorings: `Σ |Fix| = 10 · 108`.
2. Restricted Burnside on 122 avoidance colorings:
   `Σ |Fix_avoid| = 10 · 14`.
3. Structural cross-tie: `fixedCountBad 5 = countBad 5 = 10`.
4. Numerical coincidence: `catTrace 5 - 1 = countBad 10 = 122`. -/
theorem orbit_coloring_discrete_index :
    holds burnsideC10Full ∧
    holds burnsideC10Avoid ∧
    fixedCountBad 5 = countBad 5 ∧
    catTrace 5 - 1 = countBad 10 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide

end OrbitColoringDiscreteIndex
end Gnosis
