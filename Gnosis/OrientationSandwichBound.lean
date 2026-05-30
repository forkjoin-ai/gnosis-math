/-
  OrientationSandwichBound
  ========================

  A decidable  FLOOR ≤ structure ≤ CEILING  sandwich for the orientation /
  spinor / E8 theory, assembled entirely from already-proven certificates.

  The orientation symmetry ladder

      ORIENTATION → SPIN (×2 fibre {-1,+1}) → 2T/2O/2I → McKay → E6/E7/E8

  is pinned BELOW by the universal spin FLOOR (the minimal nontrivial binary
  cover, index 2) and ABOVE by the E8 CEILING (maximal exceptional Coxeter
  number 30, optimal 8-D kissing number 240). This module proves the DISCRETE
  sandwich as kernel-decidable order inequalities on already-certified constants.

  WHAT IS PROVED (discrete / order-level):

    1. cover-index FLOOR. Every binary-cover index in the ladder equals 2 — and
       2 is the minimal nontrivial cover index (a strict lower bound: a trivial
       1:1 cover has index 1 < 2; the spinor fibre {-1,+1} forces 2). The same 2
       appears at the abstract spinor fibre (`preimageOfOne.length`), the cyclic
       director quotient (`toDirector`, 2:1), and every binary→rotation cover.

    2. COXETER sandwich. The Coxeter numbers strictly ascend across the ladder
       and are sandwiched by the floor and the E8 ceiling:
              2  <  12 (E6)  <  18 (E7)  <  30 (E8)
       where the floor 2 is the spinor / rotation cover index (the h = 2 belt
       trick, 4π = 2·2π) and the ceiling 30 = `coxeterNumber .E8` = the 30
       icosahedral edges = the E8 Coxeter number (cited, SSOT). 30 is the strict
       maximum exceptional Coxeter number (F4 = 12, G2 = 6 also lie below it).

    3. KISSING / PACKING ceiling. The relevant 8-D lattice kissing number is the
       E8 root count 240 (`E8Lattice.e8Roots.length` = `E8LeechMonsterTower
       .e8RootCount`); 240 is the decidable ceiling constant, with E8 achieving
       it. Every ladder cover index, every polyhedral rotation order, and the
       Coxeter ceiling 30 all sit strictly below 240. (Above E8: the Leech
       kissing number 196560 and the Monster floor 196884 — cited, not the 8-D
       optimum, named only to mark that 240 is the *dimension-8* ceiling, not a
       global one.)

    4. `sandwich_master`. One bundle:  FLOOR ≤ ladder ≤ CEILING, tying the
       spin-floor index 2, the strictly-ascending exceptional Coxeter ladder
       2 < 12 < 18 < 30, and the kissing ceiling 240 into a single certificate.

  REUSE / CITATION. No |W|, Coxeter number, kissing number, or cover index is
  re-derived here. Coxeter numbers and Weyl orders are the `def`s of
  `DynkinCoxeterClassification` (SSOT); the kissing number 240 is the E8 root
  count of `E8Lattice` / `E8LeechMonsterTower`; the floor index 2 is
  `OrientationSpinorBridge.preimageOfOne.length` and `OrientationE8Bridge
  .spinCoverIndex`. We only state and prove the ORDER INEQUALITIES that sandwich
  the ladder between them — by kernel `decide`/`rfl`.

  AXIOM HYGIENE. Every theorem closes by KERNEL `decide`/`rfl` — never
  `native_decide`. (Imported modules may use `native_decide` for THEIR theorems,
  but this module re-proves every bound it needs by kernel reduction over the
  imported computable `def`s, so the proofs here carry at most `propext`; no
  `sorry`, no new `axiom`, no `Classical.choice`, no `Lean.ofReduceBool`.)
  Verify with `#print axioms sandwich_master`.

  SCOPE (honesty over coverage). This is the DISCRETE order sandwich only. The
  empirical PREDICTION METRIC built on top of it (fragment-sharing ≤ 240, the
  per-frame director step < π/h_k resolution corollary) is a falsifiable
  CONJECTURE developed in `docs/orientation-sandwich-metric.md`, NOT a theorem
  proved here. We prove the bounds; the metric predicts within them.
-/

import Gnosis.OrientationSpinorBridge
import Gnosis.OrientationE8Bridge
import Gnosis.OrientationADELadder
import Gnosis.E8Lattice
import Gnosis.E8LeechMonsterTower
import Gnosis.DynkinCoxeterClassification

-- The E8 root list `E8Lattice.e8Roots` constructs 240 vectors; kernel `decide`
-- over `.length = 240` reduces a 240-deep recursion (this is why the upstream
-- E8Lattice cert uses `native_decide`). We raise the kernel recursion limit so
-- the SAME fact is checked by KERNEL `decide` instead — this adds NO axiom
-- (`maxRecDepth` is an elaboration budget, not a logical assumption); the proof
-- footprint stays `propext`-at-most. Verify with `#print axioms sandwich_master`.
set_option maxRecDepth 4000

namespace Gnosis
namespace OrientationSandwichBound

open ADEMcKayCorrespondence (SU2Subgroup subgroupOrder mckayType ADEType)
open DynkinCoxeterClassification (DynkinType weylOrder coxeterNumber)
open OrientationE8Bridge (Polyhedral rotationOrder binaryCover spinCoverIndex)

-- ══════════════════════════════════════════════════════════
-- §0  The three sandwich constants, named once from the certs
-- ══════════════════════════════════════════════════════════

/-! We pin the FLOOR, the CEILING (Coxeter), and the CEILING (kissing) as named
    constants sourced from the already-proven modules, then prove the order
    inequalities between them and the ladder. Nothing here re-derives a value. -/

/-- **FLOOR.** The universal spin double-cover index, the {-1,+1} spinor fibre
    length `OrientationSpinorBridge.preimageOfOne.length = OrientationE8Bridge
    .spinCoverIndex`. It is `2`. -/
def floorIndex : Nat := spinCoverIndex

/-- The minimal NONTRIVIAL cover index: `1` is the trivial (identity) cover; the
    smallest index a genuine cover can have is `2`. The floor sits exactly here. -/
def trivialCoverIndex : Nat := 1

/-- **CEILING (Coxeter).** The maximal exceptional Coxeter number, `coxeterNumber
    .E8 = 30` (SSOT). Equals the 30 edges of the icosahedron / the E8 Coxeter
    number; cited, not re-derived. -/
def coxeterCeiling : Nat := coxeterNumber .E8 8

/-- **CEILING (kissing).** The 8-dimensional kissing / packing ceiling: the E8
    root count `240` (`E8Lattice.e8Roots.length = E8LeechMonsterTower
    .e8RootCount`), the proven-optimal 8-D kissing number (Viazovska 2016).
    Cited as a constant; E8 achieves it. -/
def kissingCeiling : Nat := E8LeechMonsterTower.e8RootCount

theorem floor_eq_two        : floorIndex = 2          := by decide
theorem coxeter_ceiling_30  : coxeterCeiling = 30     := by decide
theorem kissing_ceiling_240 : kissingCeiling = 240    := by decide

/-- The kissing ceiling constant agrees with the actual E8 root list length
    (`E8Lattice.e8Roots.length = 240`): the 240 is the E8 root system's own
    cardinality, not a bare numeral. (Kernel `decide` over the explicit root
    list reuses the construction of `E8Lattice`.) -/
theorem kissing_ceiling_is_root_count :
    kissingCeiling = E8Lattice.e8Roots.length := by decide

/-- The Coxeter ceiling constant agrees with `E8LeechMonsterTower.e8Coxeter`
    (both `30`), and with the E8 Coxeter number of the SSOT. -/
theorem coxeter_ceiling_is_e8_coxeter :
    coxeterCeiling = E8LeechMonsterTower.e8Coxeter
  ∧ coxeterCeiling = coxeterNumber .E8 8 := by
  refine ⟨by decide, rfl⟩

-- ══════════════════════════════════════════════════════════
-- §1  COVER-INDEX FLOOR — 2 ≤ every binary-cover index, all = 2
-- ══════════════════════════════════════════════════════════

/-! Every cover index in the ladder is the SAME 2 — the spinor floor. We prove
    (a) the floor is strictly above the trivial index 1 (a genuine cover);
    (b) every binary→rotation index equals 2; (c) the abstract spinor fibre and
    the director quotient also give 2; (d) hence 2 ≤ (every ladder index). -/

/-- The binary→rotation cover index for a Platonic solid: `|2P| / |P|`. -/
def coverIndex (p : Polyhedral) : Nat :=
  subgroupOrder (binaryCover p) 0 / rotationOrder p

theorem cover_index_tetra  : coverIndex .Tetra  = 2 := by decide
theorem cover_index_octa   : coverIndex .Octa   = 2 := by decide
theorem cover_index_icosa  : coverIndex .Icosa  = 2 := by decide

/-- **FLOOR is a genuine (nontrivial) cover:** `trivialCoverIndex < floorIndex`,
    i.e. `1 < 2`. The spin cover is strictly finer than the identity cover. -/
theorem floor_strictly_above_trivial : trivialCoverIndex < floorIndex := by decide

/-- **`every_cover_index_is_floor`.** Every binary-cover index in the ladder
    equals the floor `2`, and the floor equals the abstract spinor fibre length
    and the cyclic director-quotient fibre size — one universal cover index. -/
theorem every_cover_index_is_floor :
    (∀ p : Polyhedral, coverIndex p = floorIndex)
  ∧ floorIndex = OrientationSpinorBridge.preimageOfOne.length
  ∧ floorIndex = OrientationE8Bridge.directorFibreSize 0
  ∧ floorIndex = 2 := by
  refine ⟨?_, by decide, by decide, by decide⟩
  intro p; cases p <;> decide

/-- **`cover_index_floor_bound`.** The floor is a true LOWER bound: `floorIndex ≤
    (every ladder cover index)` (with equality), and the floor strictly dominates
    the trivial index. So `2 ≤ index` for every rung, and `index = 2`. -/
theorem cover_index_floor_bound :
    (∀ p : Polyhedral, floorIndex ≤ coverIndex p)
  ∧ (∀ p : Polyhedral, floorIndex = coverIndex p)
  ∧ trivialCoverIndex < floorIndex := by
  refine ⟨?_, ?_, by decide⟩
  · intro p; cases p <;> decide
  · intro p; cases p <;> decide

-- ══════════════════════════════════════════════════════════
-- §2  COXETER SANDWICH — 2 < 12 < 18 < 30 = max exceptional h
-- ══════════════════════════════════════════════════════════

/-! The exceptional Coxeter numbers strictly ascend E6 < E7 < E8, are bounded
    BELOW by the spinor / rotation floor h = 2 (the 4π belt trick), and ABOVE by
    the E8 ceiling h = 30 (the 30 icosahedral edges / E8 Coxeter number). 30 is
    the strict maximum exceptional Coxeter number. -/

/-- The Coxeter floor `h = 2`: the spinor / rotation double-cover level. The belt
    trick `4π = 2 · 2π` is the `h = 2` case — the floor the experiment confirms. -/
def coxeterFloor : Nat := 2

theorem coxeter_floor_eq_spin_index : coxeterFloor = floorIndex := by decide

/-- **`coxeter_ladder_strict_ascent`.** The exceptional Coxeter numbers strictly
    ascend: `h(E6) = 12 < h(E7) = 18 < h(E8) = 30`, reading the SSOT
    `coxeterNumber`. (Reuses the values of `OrientationADELadder
    .E8_is_max_exceptional` / `DynkinCoxeterClassification.coxeter_E*`.) -/
theorem coxeter_ladder_strict_ascent :
    coxeterNumber .E6 6 < coxeterNumber .E7 7
  ∧ coxeterNumber .E7 7 < coxeterNumber .E8 8
  ∧ coxeterNumber .E6 6 = 12
  ∧ coxeterNumber .E7 7 = 18
  ∧ coxeterNumber .E8 8 = 30 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide⟩

/-- **`coxeter_sandwich`.** The FULL Coxeter sandwich:

        floor 2  <  12 (E6)  <  18 (E7)  <  30 (E8) = ceiling,

    with the floor `coxeterFloor = 2` the spinor/rotation cover level (4π belt
    trick) and the ceiling `coxeterCeiling = coxeterNumber .E8 = 30`. The ladder
    of exceptional Coxeter numbers lies strictly inside `[2, 30]`. -/
theorem coxeter_sandwich :
    -- floor strictly below the lowest exceptional rung
    coxeterFloor < coxeterNumber .E6 6
    -- strict ascent through the exceptional ladder
  ∧ coxeterNumber .E6 6 < coxeterNumber .E7 7
  ∧ coxeterNumber .E7 7 < coxeterNumber .E8 8
    -- top rung is exactly the ceiling
  ∧ coxeterNumber .E8 8 = coxeterCeiling
    -- so every exceptional rung is sandwiched in [floor, ceiling]
  ∧ (coxeterFloor ≤ coxeterNumber .E6 6 ∧ coxeterNumber .E6 6 ≤ coxeterCeiling)
  ∧ (coxeterFloor ≤ coxeterNumber .E7 7 ∧ coxeterNumber .E7 7 ≤ coxeterCeiling)
  ∧ (coxeterFloor ≤ coxeterNumber .E8 8 ∧ coxeterNumber .E8 8 ≤ coxeterCeiling) := by
  refine ⟨by decide, by decide, by decide, by decide,
          ⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩⟩

/-- **`thirty_is_max_exceptional_coxeter`.** The ceiling `30 = h(E8)` is the
    STRICT maximum Coxeter number over ALL five exceptional types: it strictly
    exceeds h(E6)=12, h(E7)=18, h(F4)=12, h(G2)=6. So 30 is a genuine ceiling
    across the whole exceptional series, not only the E-subseries. -/
theorem thirty_is_max_exceptional_coxeter :
    coxeterNumber .E6 6 < coxeterCeiling
  ∧ coxeterNumber .E7 7 < coxeterCeiling
  ∧ coxeterNumber .F4 4 < coxeterCeiling
  ∧ coxeterNumber .G2 2 < coxeterCeiling
  ∧ coxeterCeiling = 30 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide⟩

/-- The ceiling `30` is cited as the E8 Coxeter number AND as the 30 edges of the
    icosahedron — `OrientationADELadder` selects the icosahedral A5 as the densest
    rotation group whose spin cover lands on E8, and its 30 edges equal h(E8). We
    state the numeric coincidence decidably (the geometric identification of the
    30 edges is cited from the McKay/E8 literature, not constructed here). -/
def icosahedronEdgeCount : Nat := 30

theorem icosa_edges_eq_e8_coxeter :
    icosahedronEdgeCount = coxeterCeiling
  ∧ icosahedronEdgeCount = coxeterNumber .E8 8 := by
  refine ⟨by decide, rfl⟩

-- ══════════════════════════════════════════════════════════
-- §3  KISSING / PACKING CEILING — every relevant order ≤ 240, E8 hits it
-- ══════════════════════════════════════════════════════════

/-! The 8-D kissing ceiling is 240 (E8, Viazovska-optimal). Every quantity living
    inside the orientation ladder — cover indices, polyhedral rotation orders,
    binary orders, the Coxeter ceiling 30 — sits at or below 240, and E8 achieves
    it exactly. Above E8 (Leech 196560, Monster 196884) is cited only to mark 240
    as the DIMENSION-8 ceiling, not a global one. -/

/-- **`kissing_ceiling_achieved`.** E8 ACHIEVES the kissing ceiling: the E8 root
    count equals 240 = `kissingCeiling`, on the nose (not merely ≤). -/
theorem kissing_ceiling_achieved :
    E8Lattice.e8Roots.length = kissingCeiling
  ∧ E8LeechMonsterTower.e8RootCount = kissingCeiling
  ∧ kissingCeiling = 240 := by
  refine ⟨by decide, by decide, by decide⟩

/-- **`ladder_below_kissing_ceiling`.** Every order-quantity inside the
    orientation ladder is `≤ 240 = kissingCeiling`:
      - every binary-cover index (= 2);
      - every polyhedral rotation order (12, 24, 60);
      - every binary polyhedral order (24, 48, 120);
      - the Coxeter ceiling (30).
    The densest binary order, 120 = |2I|, is exactly half the ceiling (120·2 =
    240) — the E8 roots are the 120 positive + 120 negative pairs. -/
theorem ladder_below_kissing_ceiling :
    (∀ p : Polyhedral, coverIndex p ≤ kissingCeiling)
  ∧ (∀ p : Polyhedral, rotationOrder p ≤ kissingCeiling)
  ∧ (subgroupOrder .BinaryTetra 0 ≤ kissingCeiling
      ∧ subgroupOrder .BinaryOcta 0 ≤ kissingCeiling
      ∧ subgroupOrder .BinaryIcosa 0 ≤ kissingCeiling)
  ∧ coxeterCeiling ≤ kissingCeiling
    -- the densest binary order, 120, is exactly half the kissing ceiling
  ∧ 2 * subgroupOrder .BinaryIcosa 0 = kissingCeiling := by
  refine ⟨?_, ?_, ⟨by decide, by decide, by decide⟩, by decide, by decide⟩
  · intro p; cases p <;> decide
  · intro p; cases p <;> decide

/-- **`kissing_ceiling_is_dimension_8`.** 240 is the EIGHT-dimensional ceiling,
    not a global one: above E8 sit the Leech kissing number `196560` and the
    Monster moonshine floor `196884` (both `> 240`, cited constants of
    `E8LeechMonsterTower`). We state the strict inequalities so the ceiling's
    scope is explicit — 240 bounds dimension-8 packing, the higher lattices are
    not in the orientation/E8 sandwich. -/
theorem kissing_ceiling_is_dimension_8 :
    kissingCeiling < E8LeechMonsterTower.leechKissingNumber
  ∧ E8LeechMonsterTower.leechKissingNumber < E8LeechMonsterTower.monsterFloor
  ∧ kissingCeiling = 240
  ∧ E8LeechMonsterTower.leechKissingNumber = 196560
  ∧ E8LeechMonsterTower.monsterFloor = 196884 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide⟩

-- ══════════════════════════════════════════════════════════
-- §4  sandwich_master — FLOOR ≤ ladder ≤ CEILING, one certificate
-- ══════════════════════════════════════════════════════════

/-- **`sandwich_master` — the discrete  FLOOR ≤ ladder ≤ CEILING  sandwich.**

    Bundles §1–§3 into a single kernel-decidable certificate for the
    orientation / spinor / E8 theory:

      (FLOOR, §1)
        floorIndex = 2 = (every ladder cover index) = the {-1,+1} spinor fibre,
        and `1 < 2` (a genuine, nontrivial cover) — the universal spin floor.

      (COXETER SANDWICH, §2)
        floor 2 < 12 (E6) < 18 (E7) < 30 (E8) = coxeterCeiling,
        with 30 the strict maximum exceptional Coxeter number (also > F4 = 12,
        G2 = 6) and the 30 icosahedral edges = h(E8).

      (KISSING CEILING, §3)
        every ladder order-quantity ≤ 240 = kissingCeiling = the E8 root count,
        E8 achieving 240 exactly, and `2 · |2I| = 2 · 120 = 240`. 240 is the
        dimension-8 ceiling (Leech 196560, Monster 196884 sit above, cited).

    Read as one inequality chain on the lattice of orientation invariants:
        floor (spin index 2 / belt-trick h=2)
          ≤  ladder (E6/E7/E8 Coxeter numbers, all binary covers)
          ≤  ceiling (E8: h = 30, kissing 240),
    each `≤` a kernel-checked decidable order fact, every constant cited from an
    existing certificate. -/
theorem sandwich_master :
    -- ── FLOOR (§1) ───────────────────────────────────────────
    ( floorIndex = 2
      ∧ trivialCoverIndex < floorIndex
      ∧ (∀ p : Polyhedral, floorIndex = coverIndex p)
      ∧ floorIndex = OrientationSpinorBridge.preimageOfOne.length )
    -- ── COXETER SANDWICH (§2):  2 < 12 < 18 < 30 = ceiling ────
  ∧ ( coxeterFloor < coxeterNumber .E6 6
      ∧ coxeterNumber .E6 6 < coxeterNumber .E7 7
      ∧ coxeterNumber .E7 7 < coxeterNumber .E8 8
      ∧ coxeterNumber .E8 8 = coxeterCeiling
      ∧ coxeterCeiling = 30 )
    -- ── KISSING CEILING (§3):  ladder ≤ 240, E8 hits 240 ──────
  ∧ ( (∀ p : Polyhedral, coverIndex p ≤ kissingCeiling)
      ∧ (∀ p : Polyhedral, rotationOrder p ≤ kissingCeiling)
      ∧ coxeterCeiling ≤ kissingCeiling
      ∧ E8Lattice.e8Roots.length = kissingCeiling
      ∧ 2 * subgroupOrder .BinaryIcosa 0 = kissingCeiling
      ∧ kissingCeiling = 240 )
    -- ── the sandwich, read off in one line ────────────────────
  ∧ ( floorIndex ≤ coxeterFloor          -- 2 ≤ 2  (floor index = Coxeter floor)
      ∧ coxeterFloor ≤ coxeterCeiling     -- 2 ≤ 30 (Coxeter floor ≤ Coxeter ceiling)
      ∧ coxeterCeiling ≤ kissingCeiling ) -- 30 ≤ 240 (Coxeter ceiling ≤ kissing ceiling)
:= by
  refine ⟨⟨by decide, by decide, ?_, by decide⟩,
          ⟨by decide, by decide, by decide, by decide, by decide⟩,
          ⟨?_, ?_, by decide, by decide, by decide, by decide⟩,
          ⟨by decide, by decide, by decide⟩⟩
  · intro p; cases p <;> decide
  · intro p; cases p <;> decide
  · intro p; cases p <;> decide

end OrientationSandwichBound
end Gnosis
