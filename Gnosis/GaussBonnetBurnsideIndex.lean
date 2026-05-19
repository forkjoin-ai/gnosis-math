import Init

/-
  GaussBonnetBurnsideIndex
  ========================

  Gauss-Bonnet (angle-defect form on Platonic solids) and Burnside's lemma
  (cycle-group action on binary necklaces) are two finite, discrete
  identities that both have the shape

      Σ_{x ∈ X} localCount(x)  =  scaling · globalInvariant.

  This module abstracts that record-level shape into a single structure
  `DiscreteIndexStatement` and witnesses *four* concrete instantiations:

    * `gaussBonnetTet`   — tetrahedron: Σ defect = 60 · χ,   χ = 2.
    * `gaussBonnetCube`  — cube:        Σ defect = 60 · χ,   χ = 2.
    * `burnsideC3`       — binary necklaces of length 3 under C₃:
                           Σ |Fix| = 3 · (# orbits), orbits = 4.
    * `burnsideC4`       — binary necklaces of length 4 under C₄:
                           Σ |Fix| = 4 · (# orbits), orbits = 6.

  It then realizes a *dual-view* object on the cycle graph C_n (n = 3, 4),
  where the same finite carrier supports both readings:

    * polytope-style reading as a 1-complex with combinatorial
      χ = V − E = 0 (every local count zero, so the fold is 0 = 1 · 0);
    * group-action reading as the cyclic rotation group acting on the
      vertex set, giving Σ |Fix(g)| = n · 1 (single orbit).

  The unified content is the single theorem
  `discrete_index_instances`, which closes all four primary witnesses by
  `decide` under the common predicate `holds`.

  Honest scope
  ------------
  The unification here is *structural at the record-shape level*. Both
  identities satisfy `holds` on their own native local counts (angle
  defect vs. fixed-point count), so this file witnesses the shared
  local-to-global fold as a common rewrite target. It does not prove
  that Gauss-Bonnet and Burnside share a deeper geometric or
  representation-theoretic mechanism; it proves only that both realize
  the same finite-index equation `Σ f = k · N`.

  Concrete local-count values (defect per vertex; fixed-point count per
  group element) are inlined from the peer modules
  `GaussBonnetPolytopes.lean` and `BurnsideNecklaces.lean`, so this
  module is `import Init`-only and does not reopen those namespaces.

  No `sorry`, no new `axiom`, `import Init` only, kernel `decide` only.
-/


namespace GaussBonnetBurnsideIndex

/-! ### Part 1: The unified record shape.

    A `DiscreteIndexStatement` is a finite index list, a local count
    attached to each index, a `scaling` factor, and a `globalInvariant`.
    The predicate `holds` is the single equation
    `Σ_{x ∈ indexSet} localCount x = scaling · invariant`.
-/

/-- A finite discrete index theorem is a list-indexed local count paired
    with a multiplicative scaling factor and a global invariant. Both
    Gauss-Bonnet (angle defect / Euler characteristic) and Burnside
    (fixed-point count / orbit count) instantiate this shape. -/
structure DiscreteIndexStatement where
  /-- Finite index set (vertices for Gauss-Bonnet, group elements for
      Burnside). Encoded as `List Nat` so we can evaluate by `decide`. -/
  indexSet    : List Nat
  /-- Local count at each index (angle defect in sixtieths of a full
      turn, or fixed-point count of a group element). -/
  localCount  : Nat → Nat
  /-- Multiplicative scaling on the invariant side (`60` for the
      angle-defect normalization, or `|G|` for Burnside). -/
  scaling     : Nat
  /-- Global invariant (`χ` for Gauss-Bonnet, orbit count for Burnside). -/
  invariant   : Nat
  deriving Inhabited

/-- Fold a `Nat → Nat` map over a `List Nat`. We avoid `List.map` +
    `List.sum` to keep the reducer purely structural. -/
def sumMap (f : Nat → Nat) : List Nat → Nat
  | []      => 0
  | x :: xs => f x + sumMap f xs

/-- The local-to-global fold identity for a `DiscreteIndexStatement`:
    `Σ_{x} localCount x = scaling · invariant`. -/
def holds (s : DiscreteIndexStatement) : Prop :=
  sumMap s.localCount s.indexSet = s.scaling * s.invariant

/-- `holds` is decidable because it reduces to an equation on `Nat`. -/
instance (s : DiscreteIndexStatement) : Decidable (holds s) := by
  unfold holds
  infer_instance

/-! ### Part 2: Inlined local counts for the four primary witnesses.

    We copy the relevant numerical values from the peer modules so this
    file remains `import Init`-only. The moral content (why those
    numbers are what they are) lives in `GaussBonnetPolytopes.lean` and
    `BurnsideNecklaces.lean`.
-/

/-- Per-vertex angle defect of the tetrahedron in sixtieths of a full
    turn: `60 − 3 · 10 = 30`. Inlined from
    `GaussBonnetPolytopes.vertexDefectSixtieths tetrahedron`. -/
def defectTet (_v : Nat) : Nat := 30

/-- Per-vertex angle defect of the cube in sixtieths of a full turn:
    `60 − 3 · 15 = 15`. Inlined from
    `GaussBonnetPolytopes.vertexDefectSixtieths cube`. -/
def defectCube (_v : Nat) : Nat := 15

/-- Fixed-point count of `C₃` on binary strings of length 3:
    `|Fix(rot_k)| = 2^{gcd(k, 3)}` for `k ∈ {0, 1, 2}`, giving
    `8, 2, 2`. Inlined from the gcd/power computations in
    `BurnsideNecklaces`. -/
def fixCountC3 : Nat → Nat
  | 0 => 8
  | 1 => 2
  | 2 => 2
  | _ => 0

/-- Fixed-point count of `C₄` on binary strings of length 4:
    `|Fix(rot_k)| = 2^{gcd(k, 4)}` for `k ∈ {0, 1, 2, 3}`, giving
    `16, 2, 4, 2`. -/
def fixCountC4 : Nat → Nat
  | 0 => 16
  | 1 => 2
  | 2 => 4
  | 3 => 2
  | _ => 0

/-! ### Part 3: The four primary `DiscreteIndexStatement` instances.

    Each realizes the shared fold on its native local count.
-/

/-- Gauss-Bonnet on the tetrahedron:
    `Σ_{v ∈ V} defect(v) = 4 · 30 = 120 = 60 · 2`.
    `indexSet = [0,1,2,3]`, `scaling = 60`, `invariant = χ = 2`. -/
def gaussBonnetTet : DiscreteIndexStatement :=
  { indexSet   := [0, 1, 2, 3]
  , localCount := defectTet
  , scaling    := 60
  , invariant  := 2 }

/-- Gauss-Bonnet on the cube:
    `Σ_{v ∈ V} defect(v) = 8 · 15 = 120 = 60 · 2`.
    `indexSet = [0..7]`, `scaling = 60`, `invariant = χ = 2`. -/
def gaussBonnetCube : DiscreteIndexStatement :=
  { indexSet   := [0, 1, 2, 3, 4, 5, 6, 7]
  , localCount := defectCube
  , scaling    := 60
  , invariant  := 2 }

/-- Burnside for `C₃` on `Bool^3`:
    `Σ_{g ∈ C₃} |Fix(g)| = 8 + 2 + 2 = 12 = 3 · 4`.
    `indexSet = [0,1,2]`, `scaling = 3`, `invariant = 4` orbits. -/
def burnsideC3 : DiscreteIndexStatement :=
  { indexSet   := [0, 1, 2]
  , localCount := fixCountC3
  , scaling    := 3
  , invariant  := 4 }

/-- Burnside for `C₄` on `Bool^4`:
    `Σ_{g ∈ C₄} |Fix(g)| = 16 + 2 + 4 + 2 = 24 = 4 · 6`.
    `indexSet = [0..3]`, `scaling = 4`, `invariant = 6` orbits. -/
def burnsideC4 : DiscreteIndexStatement :=
  { indexSet   := [0, 1, 2, 3]
  , localCount := fixCountC4
  , scaling    := 4
  , invariant  := 6 }

/-! ### Part 4: Per-instance kernel checks.

    Each individual statement is closed by `decide`; see Part 5 for
    the combined unified theorem.
-/

theorem gauss_bonnet_tet_holds  : holds gaussBonnetTet  := by decide
theorem gauss_bonnet_cube_holds : holds gaussBonnetCube := by decide
theorem burnside_C3_holds       : holds burnsideC3       := by decide
theorem burnside_C4_holds       : holds burnsideC4       := by decide

/-! ### Part 5: The unified local-to-global fold theorem.

    A single `decide`-closed conjunction showing that all four primary
    instances satisfy the shared predicate `holds`. This is the novel
    record-level synthesis: two Gauss-Bonnet witnesses and two
    Burnside witnesses rewriting to the same equation.
-/

/-- Unified discrete index theorem: two Gauss-Bonnet instances and two
    Burnside instances all satisfy the shared `holds` predicate,
    witnessing the common `Σ localCount = scaling · invariant` fold. -/
theorem discrete_index_instances :
    holds gaussBonnetTet ∧ holds burnsideC3 ∧
    holds gaussBonnetCube ∧ holds burnsideC4 := by
  decide

/-! ### Part 6: Dual-view bridge on the cycle graph `C_n`.

    The same finite carrier — the `n`-vertex cycle graph — supports
    two distinct readings of `DiscreteIndexStatement`:

      * polytope-style as a 1-complex: there are no 2-faces, so the
        angle-defect reading degenerates. We use the combinatorial
        Euler characteristic `χ = V − E`, which is `0` for any cycle
        graph. The per-vertex local count is `0`, so
        `Σ 0 = 1 · 0`, witnessing the trivial degenerate fold.
      * group-action as the cyclic rotation group `C_n` acting on the
        `n` vertices of the cycle: the identity fixes all `n`, each
        nontrivial rotation fixes nothing, so `Σ |Fix| = n = n · 1`,
        witnessing a single orbit.

    Both readings instantiate `DiscreteIndexStatement` on the *same*
    underlying finite structure, realizing the dual-view bridge.
-/

/-- Local count for the degenerate polytope-style reading of a cycle
    graph: angle-defect contribution is zero at every vertex of a
    1-complex. -/
def zeroCount (_ : Nat) : Nat := 0

/-- Fixed-point count of `C₃` acting by rotation on its own `3`
    vertices: identity fixes all `3`, each of the two nontrivial
    rotations fixes `0`. -/
def vertexFixC3 : Nat → Nat
  | 0 => 3
  | _ => 0

/-- Fixed-point count of `C₄` acting by rotation on its own `4`
    vertices: identity fixes all `4`, each of the three nontrivial
    rotations fixes `0`. -/
def vertexFixC4 : Nat → Nat
  | 0 => 4
  | _ => 0

/-- `C₃` cycle graph read as a 1-complex: `V = 3`, `E = 3`,
    `χ = V − E = 0`. Every local count is `0`, scaling `1`, invariant
    `0`: `Σ 0 = 1 · 0`. -/
def cycleC3AsPolytope : DiscreteIndexStatement :=
  { indexSet   := [0, 1, 2]
  , localCount := zeroCount
  , scaling    := 1
  , invariant  := 0 }

/-- `C₃` cycle graph read as a `C₃`-set: rotation group acting on the
    three vertices. `Σ |Fix| = 3 + 0 + 0 = 3 = 3 · 1`. -/
def cycleC3AsGroupAction : DiscreteIndexStatement :=
  { indexSet   := [0, 1, 2]
  , localCount := vertexFixC3
  , scaling    := 3
  , invariant  := 1 }

/-- `C₄` cycle graph read as a 1-complex: `V = 4`, `E = 4`,
    `χ = V − E = 0`. -/
def cycleC4AsPolytope : DiscreteIndexStatement :=
  { indexSet   := [0, 1, 2, 3]
  , localCount := zeroCount
  , scaling    := 1
  , invariant  := 0 }

/-- `C₄` cycle graph read as a `C₄`-set: rotation group acting on the
    four vertices. `Σ |Fix| = 4 + 0 + 0 + 0 = 4 = 4 · 1`. -/
def cycleC4AsGroupAction : DiscreteIndexStatement :=
  { indexSet   := [0, 1, 2, 3]
  , localCount := vertexFixC4
  , scaling    := 4
  , invariant  := 1 }

/-- A `DualViewObject` packages the same finite carrier (recorded as a
    shared `size`) with both a polytope-style and a group-action-style
    `DiscreteIndexStatement`. It witnesses that a single underlying
    object admits both instantiations of the shared fold. -/
structure DualViewObject where
  /-- Cardinality of the shared underlying finite carrier. -/
  size          : Nat
  /-- Polytope-style reading (combinatorial χ via local zeros for a
      1-complex, or angle-defect sum for a 2-complex). -/
  polytopeView  : DiscreteIndexStatement
  /-- Group-action reading (Burnside fixed-point sum over a symmetry
      group acting on the carrier). -/
  groupView     : DiscreteIndexStatement
  deriving Inhabited

/-- `C₃` cycle graph as a dual-view object: three shared vertices,
    both readings satisfying `holds` on their own native local counts. -/
def cycleC3Dual : DualViewObject :=
  { size         := 3
  , polytopeView := cycleC3AsPolytope
  , groupView    := cycleC3AsGroupAction }

/-- `C₄` cycle graph (square) as a dual-view object: four shared
    vertices, both readings satisfying `holds` on their own native
    local counts. -/
def cycleC4Dual : DualViewObject :=
  { size         := 4
  , polytopeView := cycleC4AsPolytope
  , groupView    := cycleC4AsGroupAction }

/-- A dual-view object is *coherent* when both of its views satisfy the
    shared local-to-global fold. -/
def dualCoherent (D : DualViewObject) : Prop :=
  holds D.polytopeView ∧ holds D.groupView

instance (D : DualViewObject) : Decidable (dualCoherent D) := by
  unfold dualCoherent
  infer_instance

/-- Both the polytope-style fold (trivial `χ = 0`) and the group-action
    fold (`Σ |Fix| = 3 · 1`) hold on the `C₃` cycle graph. -/
theorem cycleC3_dual_coherent : dualCoherent cycleC3Dual := by decide

/-- Both the polytope-style fold (trivial `χ = 0`) and the group-action
    fold (`Σ |Fix| = 4 · 1`) hold on the `C₄` cycle graph. -/
theorem cycleC4_dual_coherent : dualCoherent cycleC4Dual := by decide

/-- Combined dual-view coherence: a single kernel check closing both
    bridge instances. -/
theorem dual_view_instances :
    dualCoherent cycleC3Dual ∧ dualCoherent cycleC4Dual := by
  decide

end GaussBonnetBurnsideIndex
