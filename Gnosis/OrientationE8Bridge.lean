/-
  OrientationE8Bridge
  ===================

  The finite chain
      ORIENTATION  →  SPIN DOUBLE-COVER  →  binary icosahedral 2I  →  McKay  →  E8

  closed at the ORDER level (decidably, no continuous geometry).

  This module joins three already-proven pieces:

    * `Gnosis.OrientationSpinorBridge` — the DISCRETE 2:1 spin double cover: the
      spinor fibre {-1,+1} has length 2 (`preimageOfOne`), and the order-2 quotient
      `toDirector : Fin 4 -> Fin 2` is exactly 2:1 (`toDirector_two_to_one`). This is
      the discrete shadow of `SU(2) -> SO(3)`.
    * `ADEMcKayCorrespondence` — the finite SU(2) subgroups and McKay's bijection onto
      ADE/affine-Dynkin types; in particular `subgroupOrder .BinaryIcosa = 120`,
      `mckayType .BinaryIcosa = E8`, and the propext-only E8 SEAM theorems
      (`icosa_order_eq_E8_tower_bottom`, `burnside_2I_eq_weyl_A4`, ...).
    * `Gnosis.E8Lattice` / `DynkinCoxeterClassification` — the E8 roots, the Weyl
      coset tower `[240,56,27,16,120]`, and the SSOT for `weylOrder`, `coxeterNumber`,
      `binaryOrder`.

  WHAT IS PROVED (order-level / finite shadow):

    1. The ordinary polyhedral ROTATION groups have orders T=12, O=24, I=60.
    2. `binary_is_2to1_spin_cover`: each binary polyhedral order equals 2x its rotation
       order (120 = 2*60, 48 = 2*24, 24 = 2*12), and the doubling factor 2 EQUALS
       `OrientationSpinorBridge.preimageOfOne.length` — the concrete binary orders carry
       exactly the abstract spinor fibre {-1,+1}.
    3. `icosa_spin_cover_lands_on_E8`: the icosahedral rotation group (60), spin-doubled
       to 120, equals |2I| = the bottom of the E8 Weyl coset tower = `weylOrder .A 4`,
       and `mckayType .BinaryIcosa = E8`. Orientation's densest rotation group, doubled,
       maps to E8.
    4. `shared_cover_index_two`: the 2:1 index of `toDirector` (Fin 4 -> Fin 2) is the
       SAME 2 as the binary->rotation index — one shared spin-cover index, stated
       decidably.

  SCOPE (honesty over coverage). This formalizes only the FINITE / ORDER-LEVEL shadow
  of orientation -> spin -> E8. The continuous `SU(2) -> SO(3)` 2:1 Lie-group cover (and
  hence the genuine group-theoretic statement that 2I is the SU(2)-preimage of the
  icosahedral rotation group I < SO(3)) remains the deferred Mathlib piece that
  `OrientationSpinorBridge` names in its "Next exploration". We do NOT claim the
  continuous statement; we prove that the ORDERS line up exactly as the double cover
  demands and lock onto E8.

  AXIOM HYGIENE. Every theorem here closes by KERNEL `decide`/`rfl`/structural proof —
  NOT `native_decide`. Footprint is `propext` or none; no `sorry`, no new `axiom`, no
  `Classical.choice`.  Verify with `#print axioms <theorem>`.
-/

import Gnosis.OrientationSpinorBridge
import Gnosis.ADEMcKayCorrespondence
import Gnosis.E8Lattice
import Gnosis.DynkinCoxeterClassification

namespace Gnosis
namespace OrientationE8Bridge

open ADEMcKayCorrespondence (SU2Subgroup subgroupOrder mckayType ADEType burnsideSum2I)
open DynkinCoxeterClassification (weylOrder coxeterNumber binaryOrder affineNodeCount)

-- ══════════════════════════════════════════════════════════
-- §1  The ordinary polyhedral ROTATION groups (downstairs)
-- ══════════════════════════════════════════════════════════

/-! The orientation-preserving (rotation) symmetry groups of the Platonic solids, as
    finite subgroups of `SO(3)`:

        tetrahedral   T  =  A4   order 12
        octahedral    O  =  S4   order 24   (= cube)
        icosahedral   I  =  A5   order 60   (= dodecahedron)

    These are the DOWNSTAIRS (director / `SO(3)`) groups. Their binary `SU(2)` covers
    (2T, 2O, 2I) sit UPSTAIRS with exactly twice the order — the discrete 2:1 spin
    double cover. -/

inductive Polyhedral
  | Tetra   -- T = A4, order 12
  | Octa    -- O = S4, order 24
  | Icosa   -- I = A5, order 60
  deriving DecidableEq, BEq

/-- Order of the ordinary (rotation, orientation-preserving) polyhedral group. -/
def rotationOrder : Polyhedral → Nat
  | .Tetra => 12
  | .Octa  => 24
  | .Icosa => 60

theorem rotation_order_tetra : rotationOrder .Tetra = 12 := by decide
theorem rotation_order_octa  : rotationOrder .Octa  = 24 := by decide
theorem rotation_order_icosa : rotationOrder .Icosa = 60 := by decide

/-- The icosahedral rotation group is the densest (largest order) of the ordinary
    polyhedral rotation groups. -/
theorem icosa_is_densest_rotation :
    rotationOrder .Tetra < rotationOrder .Icosa
  ∧ rotationOrder .Octa  < rotationOrder .Icosa := by
  refine ⟨by decide, by decide⟩

/-- Pair each ordinary rotation group with its binary `SU(2)` cover. -/
def binaryCover : Polyhedral → SU2Subgroup
  | .Tetra => .BinaryTetra
  | .Octa  => .BinaryOcta
  | .Icosa => .BinaryIcosa

theorem binary_cover_tetra  : binaryCover .Tetra  = .BinaryTetra  := rfl
theorem binary_cover_octa   : binaryCover .Octa   = .BinaryOcta   := rfl
theorem binary_cover_icosa  : binaryCover .Icosa  = .BinaryIcosa  := rfl

-- ══════════════════════════════════════════════════════════
-- §2  The spin cover index = 2 = the spinor fibre {-1,+1}
-- ══════════════════════════════════════════════════════════

/-! The abstract spin-cover index is the length of the spinor fibre `{-1,+1}`, which
    `OrientationSpinorBridge.preimageOfOne` (the 2-element preimage of the squaring map's
    single director value) computes to `2`. We name it once and reuse it. -/

/-- The spin double-cover index: the length of the spinor fibre `{-1,+1}`, i.e.
    `OrientationSpinorBridge.preimageOfOne.length`. It is `2`. -/
def spinCoverIndex : Nat := OrientationSpinorBridge.preimageOfOne.length

/-- The spin cover index is `2` — the spinor fibre `{-1,+1}` has two sheets. -/
theorem spin_cover_index_eq_two : spinCoverIndex = 2 := by decide

-- ══════════════════════════════════════════════════════════
-- §3  binary_is_2to1_spin_cover — each binary order = 2 x rotation order
-- ══════════════════════════════════════════════════════════

/-- **`binary_is_2to1_spin_cover`.** For each Platonic solid, the binary `SU(2)` cover
    has order exactly `2x` the ordinary rotation-group order, and the doubling factor `2`
    EQUALS `spinCoverIndex` (= `OrientationSpinorBridge.preimageOfOne.length`, the spinor
    fibre `{-1,+1}`):

        |2I| = 120 = 2 * 60 = spinCoverIndex * |I|
        |2O| =  48 = 2 * 24 = spinCoverIndex * |O|
        |2T| =  24 = 2 * 12 = spinCoverIndex * |T|

    The concrete binary polyhedral orders carry exactly the abstract discrete double cover
    of `OrientationSpinorBridge`: the {-1,+1} sheet doubles the rotation group. -/
theorem binary_is_2to1_spin_cover :
    (subgroupOrder .BinaryIcosa 0 = 2 * rotationOrder .Icosa
      ∧ subgroupOrder .BinaryIcosa 0 = spinCoverIndex * rotationOrder .Icosa)
  ∧ (subgroupOrder .BinaryOcta 0 = 2 * rotationOrder .Octa
      ∧ subgroupOrder .BinaryOcta 0 = spinCoverIndex * rotationOrder .Octa)
  ∧ (subgroupOrder .BinaryTetra 0 = 2 * rotationOrder .Tetra
      ∧ subgroupOrder .BinaryTetra 0 = spinCoverIndex * rotationOrder .Tetra) := by
  refine ⟨⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩⟩

/-- The cover relation stated uniformly through `binaryCover`: every ordinary polyhedral
    rotation group's binary cover has order `spinCoverIndex` (= 2) times its own order. -/
theorem binary_cover_doubles_each :
    ∀ p : Polyhedral, subgroupOrder (binaryCover p) 0 = spinCoverIndex * rotationOrder p := by
  intro p; cases p <;> decide

-- ══════════════════════════════════════════════════════════
-- §4  icosa_spin_cover_lands_on_E8 — 60 -> (x2) -> 120 = 2I = E8 tower bottom
-- ══════════════════════════════════════════════════════════

/-- **`icosa_spin_cover_lands_on_E8`.** The icosahedral orientation (rotation) group,
    of order `60`, spin-doubled by the `{-1,+1}` fibre to `120`, equals:

      (a) `|2I| = subgroupOrder .BinaryIcosa = 120` — the binary icosahedral group;
      (b) the BOTTOM of the E8 Weyl coset tower `[240,56,27,16,120]`
          (`E8Lattice.cosetTower.getLastD 0`), which equals `weylOrder .A 4 = 120`;
      (c) the SSOT `binaryOrder .E8 = 120`;
      (d) and `mckayType .BinaryIcosa = E8` — McKay sends 2I to E8.

    So orientation's densest rotation group, doubled by the spin cover, maps to E8 and
    lands on the base of the E8 Weyl coset tower. This reuses the c209216 SEAM theorems
    `icosa_order_eq_E8_tower_bottom`, `icosa_order_eq_dynkin_binaryOrder`,
    `burnside_2I_eq_weyl_A4`, and `mckay_icosa`. -/
theorem icosa_spin_cover_lands_on_E8 :
    -- (a) spin-doubled icosahedral rotation order is the binary icosahedral order
    spinCoverIndex * rotationOrder .Icosa = subgroupOrder .BinaryIcosa 0
    -- (b) which is the bottom of the E8 Weyl coset tower
  ∧ subgroupOrder .BinaryIcosa 0 = (E8Lattice.cosetTower).getLastD 0
    -- the tower bottom equals |W(A4)| = 120 (the SSOT weylOrder)
  ∧ (E8Lattice.cosetTower).getLastD 0 = weylOrder .A 4
    -- (c) and equals the SSOT binaryOrder for E8
  ∧ subgroupOrder .BinaryIcosa 0 = binaryOrder .E8 8
    -- (d) McKay sends 2I to E8
  ∧ mckayType .BinaryIcosa = ADEType.E8 := by
  refine ⟨by decide, by decide, by decide, by decide, rfl⟩

/-- The full numeric chain `60 -> 120 -> E8` as a single equality run:
    `spinCoverIndex * 60 = |2I| = tower bottom = |W(A4)| = burnsideSum2I = 120`. -/
theorem icosa_chain_numbers :
    spinCoverIndex * rotationOrder .Icosa = 120
  ∧ subgroupOrder .BinaryIcosa 0 = 120
  ∧ (E8Lattice.cosetTower).getLastD 0 = 120
  ∧ weylOrder .A 4 = 120
  ∧ burnsideSum2I = 120 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide⟩

/-- |Irr(2I)| = 9 = #nodes of the affine Ẽ8 diagram, and the affine marks of Ẽ8 sum to
    `coxeterNumber .E8 = 30`: the E8 side of the seam, reused from the c209216 theorems. -/
theorem icosa_affine_E8_seam :
    ADEMcKayCorrespondence.irrepCount .BinaryIcosa 0 = affineNodeCount .E8 8
  ∧ ADEMcKayCorrespondence.E8_tilde_marks.foldl (· + ·) 0 = coxeterNumber .E8 8 := by
  refine ⟨by decide, by decide⟩

-- ══════════════════════════════════════════════════════════
-- §5  shared_cover_index_two — the SAME 2:1 index upstairs and downstairs
-- ══════════════════════════════════════════════════════════

/-! The cyclic quotient `OrientationSpinorBridge.toDirector : Fin 4 -> Fin 2` is 2:1:
    each director value has a 2-element fibre (`toDirector_two_to_one`). The binary ->
    rotation cover is ALSO 2:1 (`binary_is_2to1_spin_cover`). We state, decidably, that
    these are the same index `2` — one shared spin-cover index across the abstract
    quotient and the concrete polyhedral cover. -/

/-- The fibre size of the cyclic quotient `toDirector` over director `0` (resp. `1`):
    `2`, computed exactly as in `OrientationSpinorBridge.toDirector_two_to_one`. -/
def directorFibreSize (d : OrientationSpinorBridge.Director) : Nat :=
  (([0,1,2,3] : List OrientationSpinorBridge.Sheet).filter
    (fun x => decide (OrientationSpinorBridge.toDirector x = d))).length

/-- **`shared_cover_index_two`.** All three 2:1 indices coincide on the value `2`:

      (a) the cyclic quotient `toDirector : Fin 4 -> Fin 2` has fibre size `2` over each
          director value (the `OrientationSpinorBridge.toDirector_two_to_one` count);
      (b) the spinor fibre `{-1,+1}` (`preimageOfOne`) has length `2` (= `spinCoverIndex`);
      (c) the binary->rotation index is `2`: `|2I| / |I| = 120 / 60 = 2`, and likewise
          `|2O| / |O| = |2T| / |T| = 2`.

    The 2:1 of the abstract director quotient is the SAME `2` as the concrete binary->
    rotation spin cover. One shared cover index. -/
theorem shared_cover_index_two :
    -- (a) cyclic quotient fibre size is 2 over each director value
    (directorFibreSize 0 = 2 ∧ directorFibreSize 1 = 2)
    -- (b) the spinor fibre length is 2 (= spinCoverIndex)
  ∧ (spinCoverIndex = 2 ∧ OrientationSpinorBridge.preimageOfOne.length = 2)
    -- (c) the binary->rotation index is 2 for all three solids
  ∧ (subgroupOrder .BinaryIcosa 0 / rotationOrder .Icosa = 2
      ∧ subgroupOrder .BinaryOcta 0 / rotationOrder .Octa = 2
      ∧ subgroupOrder .BinaryTetra 0 / rotationOrder .Tetra = 2)
    -- and all of these equal one another (the shared index)
  ∧ directorFibreSize 0 = spinCoverIndex
  ∧ spinCoverIndex = subgroupOrder .BinaryIcosa 0 / rotationOrder .Icosa := by
  refine ⟨⟨by decide, by decide⟩, ⟨by decide, by decide⟩,
          ⟨by decide, by decide, by decide⟩, by decide, by decide⟩

/-- The abstract `OrientationSpinorBridge.toDirector_two_to_one` (Fin 4 -> Fin 2, both
    fibres length 2) reused verbatim, tying this module's `directorFibreSize` to the
    spinor-bridge cert. -/
theorem director_fibres_match_spinor_bridge :
    directorFibreSize 0 = 2 ∧ directorFibreSize 1 = 2
  ∧ (([0,1,2,3] : List OrientationSpinorBridge.Sheet).filter
        (fun x => decide (OrientationSpinorBridge.toDirector x = 0))).length = 2
  ∧ (([0,1,2,3] : List OrientationSpinorBridge.Sheet).filter
        (fun x => decide (OrientationSpinorBridge.toDirector x = 1))).length = 2 := by
  refine ⟨by decide, by decide,
          (OrientationSpinorBridge.toDirector_two_to_one).1,
          (OrientationSpinorBridge.toDirector_two_to_one).2⟩

-- ══════════════════════════════════════════════════════════
-- §6  Master certificate — the closed finite chain
-- ══════════════════════════════════════════════════════════

/-- **ORIENTATION → SPIN → 2I → E8 (finite / order-level shadow).**

      (1) §3  Each binary polyhedral order is `2x` its rotation order, the `2` being the
              spinor fibre `{-1,+1}` (`binary_is_2to1_spin_cover`): the {-1,+1} sheet of
              `OrientationSpinorBridge` doubles the orientation (rotation) group.
      (2) §4  The icosahedral rotation group (60), spin-doubled to 120, equals `|2I|`,
              the bottom of the E8 Weyl coset tower `= |W(A4)|`, and `mckayType 2I = E8`
              (`icosa_spin_cover_lands_on_E8`).
      (3) §5  The cyclic quotient `toDirector : Fin 4 -> Fin 2` and the binary->rotation
              cover share the SAME 2:1 index `2` (`shared_cover_index_two`).

    This is the FINITE shadow only; the continuous `SU(2) -> SO(3)` cover is deferred (see
    `OrientationSpinorBridge`'s Next exploration). -/
theorem orientation_E8_bridge_master :
    -- (1) spin cover doubles each rotation group, factor = spinor fibre {-1,+1}
    (∀ p : Polyhedral, subgroupOrder (binaryCover p) 0 = spinCoverIndex * rotationOrder p)
  ∧ spinCoverIndex = OrientationSpinorBridge.preimageOfOne.length
    -- (2) icosahedral 60 -> 120 = |2I| = E8 tower bottom = |W(A4)|, McKay sends 2I to E8
  ∧ (spinCoverIndex * rotationOrder .Icosa = subgroupOrder .BinaryIcosa 0
      ∧ subgroupOrder .BinaryIcosa 0 = (E8Lattice.cosetTower).getLastD 0
      ∧ (E8Lattice.cosetTower).getLastD 0 = weylOrder .A 4
      ∧ mckayType .BinaryIcosa = ADEType.E8)
    -- (3) shared 2:1 cover index between toDirector quotient and binary->rotation
  ∧ (directorFibreSize 0 = spinCoverIndex
      ∧ spinCoverIndex = subgroupOrder .BinaryIcosa 0 / rotationOrder .Icosa) := by
  refine ⟨binary_cover_doubles_each, by decide,
          ⟨by decide, by decide, by decide, rfl⟩, by decide, by decide⟩

-- ══════════════════════════════════════════════════════════
-- §7  Reading
-- ══════════════════════════════════════════════════════════

/-! The finite chain
        ORIENTATION  →  SPIN (×2 fibre {-1,+1})  →  2I  →  McKay  →  E8
    closed at the order level.

    The ordinary (orientation-preserving) icosahedral rotation group `I` has order `60`
    (§1). The discrete spin double cover of `OrientationSpinorBridge` supplies the `{-1,+1}`
    sheet, whose fibre `preimageOfOne` has length `2` (§2). Doubling: `2 * 60 = 120 = |2I|`,
    the binary icosahedral group (§3, `binary_is_2to1_spin_cover`), and likewise `O -> 2O`,
    `T -> 2T`. The order-120 binary icosahedral group is, by McKay, the E8 type, and `120`
    is the bottom of the E8 Weyl coset tower `[240,56,27,16,120] = |W(A4)|` (§4,
    `icosa_spin_cover_lands_on_E8`, reusing the c209216 SEAM). The 2:1 index of the abstract
    director quotient `Fin 4 -> Fin 2` is the SAME `2` as the binary->rotation index (§5,
    `shared_cover_index_two`).

    SCOPE. Only the ORDER-LEVEL / finite shadow is proved. We do NOT build the continuous
    `SU(2) -> SO(3)` Lie-group cover, and we do NOT claim the group-theoretic statement that
    2I is the literal SU(2)-preimage of `I < SO(3)` — that needs Mathlib (real-manifold Lie
    theory), and is the deferred piece `OrientationSpinorBridge` names. What is machine-
    checked is that the orders line up EXACTLY as a 2:1 cover demands and lock onto E8.

    -- Next exploration:
    --   With Mathlib, lift §3 from an order equality to a genuine group statement: build
    --   the central extension `1 -> {-1,+1} -> 2I -> I -> 1` (the SU(2)-preimage of the
    --   icosahedral rotation group under the continuous `SU(2) -> SO(3)` cover deferred in
    --   `OrientationSpinorBridge`), and prove its order is `2 * |A5| = 120` AS A CONSEQUENCE
    --   of the cover, not as a tabulated number. Then `binary_is_2to1_spin_cover` becomes a
    --   theorem about kernels rather than about `subgroupOrder`, and the chain
    --   orientation -> spin -> 2I -> E8 is closed at the group level, not just the order
    --   level. The hard part remains the continuous cover and its `{-1,+1}` kernel.
-/

end OrientationE8Bridge
end Gnosis
