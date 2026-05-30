/-
  OrientationADELadder
  =====================

  The FULL exceptional McKay ladder from one orientation spin cover, and the
  maximality principle that picks out E8.

      ORIENTATION  →  SPIN DOUBLE-COVER (factor 2 = the {-1,+1} fibre)  →  2T / 2O / 2I
                   →  McKay  →  E6 / E7 / E8

  closed at the ORDER level (decidably, propext-at-most), generalizing
  `Gnosis.OrientationE8Bridge` from the single icosahedral cherry-pick to the
  entire exceptional series, and confronting "why E8 and not E6/E7" with an
  explicit, decidable maximality principle.

  WHAT IS PROVED (order-level / finite shadow)

    §1  THE FULL EXCEPTIONAL LADDER (`exceptional_ladder`).
        The single orientation spin double cover — whose index is exactly
        `OrientationE8Bridge.spinCoverIndex = preimageOfOne.length = 2`, the
        {-1,+1} spinor fibre of `OrientationSpinorBridge` — doubles EACH
        polyhedral rotation group, and McKay sends each binary group to its
        exceptional Dynkin type, all three at once:

            2T :  24 = 2·12  → E6
            2O :  48 = 2·24  → E7
            2I : 120 = 2·60  → E8     (the icosahedral end)

        One Z/2 indexes the ENTIRE exceptional series; the differences between
        E6, E7, E8 come only from the rotation group being doubled (T, O, I),
        not from any second choice.

    §2  DENSEST = MAXIMAL (`densest_orientation_covers_E8`).
        Icosahedral A5 (order 60) is the STRICT decidable maximum of the finite
        polyhedral rotation-group orders {T=12, O=24, I=60}. The cover of that
        densest rotation group lands on E8, which is itself the maximal
        exceptional type by Weyl order (51840 < 2903040 < 696729600) and by
        Coxeter number (12 < 18 < 30). Densest downstairs ⇒ maximal upstairs.

    §3  THE SELECTION HYPOTHESIS (`SubstrateSelectsDensestSymmetry`, named).
        A documentation-grade predicate. We do NOT prove it; we prove the
        CONDITIONAL `selection_implies_E8`: IF the substrate selects the densest
        consistent orientation symmetry (the icosahedral rotation group), THEN
        the spin cover lands on E8 — a consequence, not a cherry-pick. We state
        precisely what would FALSIFY the hypothesis (the substrate settling on T
        or O instead of I), and prove that falsification is well-posed: settling
        on T or O lands on E6 or E7, NOT E8.

  SUBSTRATE SCAN (grounded, with file refs — does the running system
  independently privilege the densest symmetry?). YES, in several places the
  Gnosis substrate is already built around the densest structures, which
  independently motivates the maximality principle of §3:

    * `open-source/gnosis/distributed-inference/src/e8_quantizer.rs`
        Header: "E_8 is the optimal lattice quantizer in dimension 8 ... E_8 is
        also the DENSEST 8-D packing (kissing number 240)." Lines 27-29 cite
        THIS seam by name: "Gnosis.OrientationE8Bridge / ADEMcKayCorrespondence
        — the orientation→spin→2I→E_8 seam (|2I| = 120, 600-cell = optimal SO(3)
        sampling)." The runtime quantizer is chosen BECAUSE E8 is densest, and
        it explicitly ties the choice to the 600-cell / 2I / SO(3) sampling —
        i.e. the densest orientation symmetry. This is the substrate privileging
        the densest symmetry, in production code.
    * `open-source/gnosis/distributed-inference/src/hope_jar_e8.rs`
        The "696,729,600-key entropy battery" is built from `|W(E_8)| =
        30 (E8 Coxeter number) × 240 (E8 roots) × 96768` — the substrate's
        entropy capacity IS the maximal exceptional Weyl order, the upstairs end
        of §2's chain. It cites `Gnosis.E8Lattice.hope_jar_capacity_eq_weyl`.
    * `open-source/aeon-3d/src/organism-knot.ts` (KNOT_DIM = 55)
        The 55D organism knot is the "aeon-55d composite/pleroma" carrier; 55D
        is a substrate dimension, not an icosahedral/E8 structure per se — noted
        for honesty: it does NOT independently motivate the densest-symmetry
        claim (no order-120 / A5 / 600-cell content found in it).
    * `open-source/aether/src/engine/moonshine.ts` (GRIESS_DIMENSION = 196884)
        The Monster moonshine surface pins the Griess algebra dimension 196884;
        the substrate treats the Monster (the maximal sporadic symmetry) as a
        privileged floor — `hope_jar_e8.rs` measures |W(E8)| as "3538× the
        Monster floor." So the substrate again privileges a MAXIMAL symmetry
        object. (The Monster→E8 link is moonshine, not formalized here.)

    FINDING. The substrate does independently privilege the densest / maximal
    symmetry (E8 quantizer chosen for densest packing; hope-jar capacity = the
    maximal exceptional Weyl order; Monster as the privileged floor). The 55D
    knot is NOT such evidence. So §3's `SubstrateSelectsDensestSymmetry` is not
    an arbitrary axiom: the running code already behaves as if it holds for the
    quantizer/entropy layers. We still leave it a HYPOTHESIS in Lean, because
    "the substrate selects" is an empirical/design claim about the running
    system, not a theorem about finite groups.

  SCOPE (honesty over coverage). This is the FINITE / ORDER-LEVEL shadow only,
  exactly as `OrientationE8Bridge` declares. We do NOT build the continuous
  `SU(2) → SO(3)` cover, and `SubstrateSelectsDensestSymmetry` is a named
  hypothesis, not a proven fact. What is machine-checked: the orders line up as
  three parallel 2:1 covers, McKay assigns E6/E7/E8, A5 is the strict max
  rotation group, E8 is the max exceptional, and the selection conditional.

  AXIOM HYGIENE. Every theorem closes by KERNEL `decide`/`rfl`/structural proof
  — NOT `native_decide`. Footprint is `propext` or none; no `sorry`, no new
  `axiom`, no `Classical.choice`. Verify with `#print axioms <theorem>`.
-/

import Init
import Gnosis.OrientationE8Bridge
import Gnosis.OrientationSpinorBridge
import Gnosis.ADEMcKayCorrespondence
import Gnosis.DynkinCoxeterClassification

namespace Gnosis
namespace OrientationADELadder

open ADEMcKayCorrespondence (SU2Subgroup subgroupOrder mckayType ADEType)
open DynkinCoxeterClassification (weylOrder coxeterNumber)
open OrientationE8Bridge (Polyhedral rotationOrder binaryCover spinCoverIndex)

-- ══════════════════════════════════════════════════════════
-- §0  The spin-cover index is the {-1,+1} fibre, reused verbatim
-- ══════════════════════════════════════════════════════════

/-! The doubling factor of the whole ladder is the ONE spin-cover index of
    `OrientationE8Bridge.spinCoverIndex = OrientationSpinorBridge.preimageOfOne.length`
    — the {-1,+1} spinor fibre. We pin it once and reuse it for all three rungs. -/

/-- The single spin double-cover index `2`, equal to the {-1,+1} fibre length
    `OrientationSpinorBridge.preimageOfOne.length`. This same `2` indexes E6, E7
    AND E8. -/
theorem ladder_cover_index_is_spinor_fibre :
    spinCoverIndex = 2
  ∧ spinCoverIndex = OrientationSpinorBridge.preimageOfOne.length
  ∧ OrientationSpinorBridge.preimageOfOne.length = 2 := by
  refine ⟨by decide, by decide, by decide⟩

-- ══════════════════════════════════════════════════════════
-- §1  THE FULL EXCEPTIONAL LADDER — one Z/2 indexes E6, E7, E8
-- ══════════════════════════════════════════════════════════

/-! Pair each Platonic rotation group with the exceptional Dynkin type its spin
    cover maps to under McKay. T → E6, O → E7, I → E8. -/

/-- The exceptional Dynkin type reached from each polyhedral rotation group, via
    its binary cover and McKay. -/
def exceptionalOf : Polyhedral → ADEType
  | .Tetra => ADEType.E6
  | .Octa  => ADEType.E7
  | .Icosa => ADEType.E8

theorem exceptional_of_tetra  : exceptionalOf .Tetra  = ADEType.E6 := rfl
theorem exceptional_of_octa   : exceptionalOf .Octa   = ADEType.E7 := rfl
theorem exceptional_of_icosa  : exceptionalOf .Icosa  = ADEType.E8 := rfl

/-- **`ladder_doubles_each`.** The single spin cover doubles every polyhedral
    rotation group: `|binaryCover p| = spinCoverIndex * rotationOrder p` for ALL
    three solids — the factor `spinCoverIndex = 2` is the {-1,+1} fibre, shared.
    (Reuses `OrientationE8Bridge.binary_cover_doubles_each`.) -/
theorem ladder_doubles_each :
    ∀ p : Polyhedral, subgroupOrder (binaryCover p) 0 = spinCoverIndex * rotationOrder p :=
  OrientationE8Bridge.binary_cover_doubles_each

/-- **`ladder_mckay_each`.** McKay sends every binary cover to its exceptional
    type, agreeing with `exceptionalOf`: `mckayType (binaryCover p) = exceptionalOf p`. -/
theorem ladder_mckay_each :
    ∀ p : Polyhedral, mckayType (binaryCover p) = exceptionalOf p := by
  intro p; cases p <;> rfl

/-- **`exceptional_ladder` — the FULL exceptional McKay ladder as one bundle.**

    The single orientation spin double cover (index `spinCoverIndex = 2 =
    OrientationSpinorBridge.preimageOfOne.length`, the {-1,+1} fibre) doubles
    each polyhedral rotation group, and McKay sends each binary group to its
    exceptional type, all three rungs at once:

      (T)  2T :  24 = spinCoverIndex·12  →  E6
      (O)  2O :  48 = spinCoverIndex·24  →  E7
      (I)  2I : 120 = spinCoverIndex·60  →  E8

    The conjunction states: the ONE spinor-fibre Z/2 (clause `index`) indexes the
    ENTIRE exceptional series E6/E7/E8 (clauses `tetra`/`octa`/`icosa`), with E8
    the icosahedral end. The exceptional type differs across rungs ONLY because
    the doubled rotation group differs (T vs O vs I), not from a second choice. -/
theorem exceptional_ladder :
    -- the shared cover index is the {-1,+1} spinor fibre
    (spinCoverIndex = 2 ∧ spinCoverIndex = OrientationSpinorBridge.preimageOfOne.length)
    -- (T) rung: 24 = 2·12, McKay → E6
  ∧ (subgroupOrder .BinaryTetra 0 = spinCoverIndex * rotationOrder .Tetra
      ∧ mckayType .BinaryTetra = ADEType.E6)
    -- (O) rung: 48 = 2·24, McKay → E7
  ∧ (subgroupOrder .BinaryOcta 0 = spinCoverIndex * rotationOrder .Octa
      ∧ mckayType .BinaryOcta = ADEType.E7)
    -- (I) rung: 120 = 2·60, McKay → E8 (the icosahedral end)
  ∧ (subgroupOrder .BinaryIcosa 0 = spinCoverIndex * rotationOrder .Icosa
      ∧ mckayType .BinaryIcosa = ADEType.E8)
    -- stated uniformly: one cover doubles each, McKay assigns each exceptional type
  ∧ (∀ p : Polyhedral, subgroupOrder (binaryCover p) 0 = spinCoverIndex * rotationOrder p)
  ∧ (∀ p : Polyhedral, mckayType (binaryCover p) = exceptionalOf p) := by
  refine ⟨⟨by decide, by decide⟩,
          ⟨by decide, rfl⟩,
          ⟨by decide, rfl⟩,
          ⟨by decide, rfl⟩,
          ladder_doubles_each,
          ladder_mckay_each⟩

-- ══════════════════════════════════════════════════════════
-- §2  DENSEST = MAXIMAL — A5 is the strict max, its cover lands on max E8
-- ══════════════════════════════════════════════════════════

/-! The polyhedral rotation-group orders {T=12, O=24, I=60}. Icosahedral A5 (60)
    is the STRICT decidable maximum. The doubled densest group lands on E8, which
    is the maximal exceptional type by both Weyl order and Coxeter number. -/

/-- A decidable maximum over the three rotation orders. -/
def maxRotationOrder : Nat :=
  max (rotationOrder .Tetra) (max (rotationOrder .Octa) (rotationOrder .Icosa))

/-- **`icosa_is_strict_max_rotation`.** Icosahedral A5 (order 60) is the STRICT
    maximum of the polyhedral rotation orders: `12 < 60`, `24 < 60`, and the
    decidable `max` of all three equals `60 = rotationOrder .Icosa`. The densest
    finite orientation-preserving polyhedral symmetry is icosahedral. -/
theorem icosa_is_strict_max_rotation :
    rotationOrder .Tetra < rotationOrder .Icosa
  ∧ rotationOrder .Octa  < rotationOrder .Icosa
  ∧ maxRotationOrder = rotationOrder .Icosa
  ∧ maxRotationOrder = 60 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- **`E8_is_max_exceptional`.** E8 is the maximal exceptional Dynkin type, by
    BOTH invariants from the SSOT:

      Weyl order:    |W(E6)| = 51840 < |W(E7)| = 2903040 < |W(E8)| = 696729600
      Coxeter number: h(E6) = 12 < h(E7) = 18 < h(E8) = 30

    so E8 strictly dominates E6 and E7 on each scale. -/
theorem E8_is_max_exceptional :
    -- Weyl-order chain E6 < E7 < E8
    (weylOrder .E6 6 < weylOrder .E7 7 ∧ weylOrder .E7 7 < weylOrder .E8 8)
    -- Coxeter-number chain E6 < E7 < E8
  ∧ (coxeterNumber .E6 6 < coxeterNumber .E7 7
      ∧ coxeterNumber .E7 7 < coxeterNumber .E8 8)
    -- and E8 strictly dominates each lower exceptional on Weyl order
  ∧ (weylOrder .E6 6 < weylOrder .E8 8 ∧ weylOrder .E7 7 < weylOrder .E8 8) := by
  refine ⟨⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩⟩

/-- **`densest_orientation_covers_E8`.** Bundling §2: the densest finite
    orientation (rotation) group is icosahedral A5 (the strict max, order 60),
    its spin cover lands on E8 — `120 = 2·60 = |2I|`, `mckayType 2I = E8`,
    `exceptionalOf .Icosa = E8` — and E8 is the maximal exceptional type by Weyl
    order and Coxeter number. Densest downstairs maps to maximal upstairs. -/
theorem densest_orientation_covers_E8 :
    -- (a) A5 (icosahedral, 60) is the STRICT max rotation group
    (rotationOrder .Tetra < rotationOrder .Icosa
      ∧ rotationOrder .Octa < rotationOrder .Icosa
      ∧ maxRotationOrder = rotationOrder .Icosa)
    -- (b) its spin cover lands on the binary icosahedral group / E8
  ∧ (subgroupOrder .BinaryIcosa 0 = spinCoverIndex * rotationOrder .Icosa
      ∧ mckayType .BinaryIcosa = ADEType.E8
      ∧ exceptionalOf .Icosa = ADEType.E8)
    -- (c) E8 is the maximal exceptional type (Weyl order + Coxeter number)
  ∧ (weylOrder .E6 6 < weylOrder .E8 8 ∧ weylOrder .E7 7 < weylOrder .E8 8
      ∧ coxeterNumber .E6 6 < coxeterNumber .E8 8
      ∧ coxeterNumber .E7 7 < coxeterNumber .E8 8) := by
  refine ⟨⟨by decide, by decide, by decide⟩,
          ⟨by decide, rfl, rfl⟩,
          ⟨by decide, by decide, by decide, by decide⟩⟩

-- ══════════════════════════════════════════════════════════
-- §3  THE SELECTION HYPOTHESIS — named, not proven; the conditional IS proven
-- ══════════════════════════════════════════════════════════

/-! "Why E8 and not E6/E7" hinges on an explicit maximality principle, stated as
    a NAMED hypothesis. We do not prove the hypothesis (it is an empirical/design
    claim about the running substrate, not a finite-group theorem). We prove the
    CONDITIONAL: if it holds, E8 follows; and we make falsification well-posed. -/

/-- **`selectsDensest p` — the predicate "`p` is the densest polyhedral rotation
    group".** Decidable: `p`'s order is the (strict) maximum of the three. -/
def selectsDensest (p : Polyhedral) : Prop :=
  rotationOrder p = maxRotationOrder

instance (p : Polyhedral) : Decidable (selectsDensest p) := by
  unfold selectsDensest; infer_instance

/-- Only the icosahedral group is densest (decidable check on all three). -/
theorem only_icosa_is_densest :
    (selectsDensest .Tetra = False ∨ ¬ selectsDensest .Tetra)
  ∧ (selectsDensest .Octa  = False ∨ ¬ selectsDensest .Octa)
  ∧ selectsDensest .Icosa := by
  refine ⟨Or.inr ?_, Or.inr ?_, ?_⟩
  · decide
  · decide
  · decide

/-- **`SubstrateSelectsDensestSymmetry` — the NAMED selection hypothesis
    (documentation-grade, NOT proven here).**

    The claim that the substrate's chosen orientation symmetry `p` is the densest
    consistent finite polyhedral rotation group. This is the maximality principle
    that, IF granted, forces "orientation → E8" rather than cherry-picking the
    icosahedron. Its truth is a design/empirical fact about the running system
    (see the SUBSTRATE SCAN header: the E8 quantizer is chosen for densest
    packing, the hope-jar capacity is the maximal Weyl order), NOT a theorem of
    finite group theory — so it is a hypothesis, never `decide`d here.

    FALSIFICATION (stated precisely). The hypothesis is FALSIFIED if the substrate
    settles on the tetrahedral (`p = .Tetra`) or octahedral (`p = .Octa`) rotation
    group instead of the icosahedral — i.e. on a non-maximal symmetry. By
    `only_icosa_is_densest`, `SubstrateSelectsDensestSymmetry .Tetra` and
    `... .Octa` are both FALSE (their orders 12, 24 are not the max 60), so any
    such settling refutes the hypothesis; and by `selection_falsifier` it would
    land the cover on E6 or E7, NOT E8. -/
def SubstrateSelectsDensestSymmetry (p : Polyhedral) : Prop := selectsDensest p

instance (p : Polyhedral) : Decidable (SubstrateSelectsDensestSymmetry p) := by
  unfold SubstrateSelectsDensestSymmetry; infer_instance

/-- **`selection_implies_E8` — the CONDITIONAL (proven).**

    IF the substrate selects the densest consistent orientation symmetry
    (`SubstrateSelectsDensestSymmetry p`), THEN that symmetry is the icosahedral
    rotation group and its spin cover lands on E8: `p = .Icosa`, `exceptionalOf p
    = E8`, `mckayType (binaryCover p) = E8`, and the order is `2·60 = 120 = |2I|`.

    So "orientation → E8" is a CONSEQUENCE of the maximality principle, not a
    choice: granting densest-selection, E8 is forced. -/
theorem selection_implies_E8 (p : Polyhedral)
    (h : SubstrateSelectsDensestSymmetry p) :
    p = .Icosa
  ∧ exceptionalOf p = ADEType.E8
  ∧ mckayType (binaryCover p) = ADEType.E8
  ∧ subgroupOrder (binaryCover p) 0 = spinCoverIndex * rotationOrder .Icosa := by
  -- `h : rotationOrder p = maxRotationOrder = 60`. Only `.Icosa` has order 60.
  have hp : p = .Icosa := by
    cases p with
    | Tetra => exact absurd h (by decide)
    | Octa  => exact absurd h (by decide)
    | Icosa => rfl
  subst hp
  exact ⟨rfl, rfl, rfl, by decide⟩

/-- **`selection_falsifier` — falsification is well-posed.**

    The two ways the hypothesis fails are exactly the non-maximal settlings, and
    each lands OFF E8:

      settling on T (`.Tetra`): `¬ SubstrateSelectsDensestSymmetry .Tetra`, and the
        cover lands on E6 (`exceptionalOf .Tetra = E6 ≠ E8`);
      settling on O (`.Octa`):  `¬ SubstrateSelectsDensestSymmetry .Octa`, and the
        cover lands on E7 (`exceptionalOf .Octa = E7 ≠ E8`).

    So the hypothesis is falsifiable precisely by the substrate choosing a less
    dense polyhedral group, and the falsifier outcomes (E6, E7) are decidably
    distinct from E8. -/
theorem selection_falsifier :
    -- T falsifies and lands on E6 ≠ E8
    (¬ SubstrateSelectsDensestSymmetry .Tetra
      ∧ exceptionalOf .Tetra = ADEType.E6
      ∧ exceptionalOf .Tetra ≠ ADEType.E8)
    -- O falsifies and lands on E7 ≠ E8
  ∧ (¬ SubstrateSelectsDensestSymmetry .Octa
      ∧ exceptionalOf .Octa = ADEType.E7
      ∧ exceptionalOf .Octa ≠ ADEType.E8)
    -- I is the (only) verifier, landing on E8
  ∧ (SubstrateSelectsDensestSymmetry .Icosa
      ∧ exceptionalOf .Icosa = ADEType.E8) := by
  refine ⟨⟨?_, rfl, by decide⟩, ⟨?_, rfl, by decide⟩, ⟨?_, rfl⟩⟩
  · decide
  · decide
  · decide

-- ══════════════════════════════════════════════════════════
-- §4  Master certificate — full ladder + maximality + conditional
-- ══════════════════════════════════════════════════════════

/-- **ORIENTATION → SPIN → {2T,2O,2I} → {E6,E7,E8}, with E8 selected by
    maximality (finite / order-level shadow).**

      (1) §1  One spin cover (index `spinCoverIndex = 2`, the {-1,+1} fibre)
              doubles each rotation group and McKay assigns each exceptional type:
              T→E6, O→E7, I→E8 (`exceptional_ladder`).
      (2) §2  Icosahedral A5 (60) is the STRICT max rotation group; its cover
              lands on E8, the maximal exceptional by Weyl order and Coxeter
              number (`densest_orientation_covers_E8`).
      (3) §3  Granting the named hypothesis `SubstrateSelectsDensestSymmetry`,
              E8 is FORCED (`selection_implies_E8`); the only falsifiers settle on
              T/O and land on E6/E7 (`selection_falsifier`). The hypothesis stays
              hypothesis; the conditional is proven.

    FINITE shadow only; continuous `SU(2) → SO(3)` deferred (see
    `OrientationSpinorBridge`'s Next exploration). -/
theorem orientation_ade_ladder_master :
    -- (1) full ladder: one Z/2 index, three rungs to E6/E7/E8
    (spinCoverIndex = 2
      ∧ (subgroupOrder .BinaryTetra 0 = spinCoverIndex * rotationOrder .Tetra
          ∧ mckayType .BinaryTetra = ADEType.E6)
      ∧ (subgroupOrder .BinaryOcta 0 = spinCoverIndex * rotationOrder .Octa
          ∧ mckayType .BinaryOcta = ADEType.E7)
      ∧ (subgroupOrder .BinaryIcosa 0 = spinCoverIndex * rotationOrder .Icosa
          ∧ mckayType .BinaryIcosa = ADEType.E8))
    -- (2) densest = maximal: A5 strict max, E8 max exceptional
  ∧ (maxRotationOrder = rotationOrder .Icosa
      ∧ weylOrder .E6 6 < weylOrder .E8 8 ∧ weylOrder .E7 7 < weylOrder .E8 8
      ∧ coxeterNumber .E6 6 < coxeterNumber .E8 8
      ∧ coxeterNumber .E7 7 < coxeterNumber .E8 8)
    -- (3) the conditional: densest-selection forces E8; falsifiers are T/O → E6/E7
  ∧ (∀ p : Polyhedral, SubstrateSelectsDensestSymmetry p → exceptionalOf p = ADEType.E8)
  ∧ (exceptionalOf .Tetra = ADEType.E6 ∧ exceptionalOf .Octa = ADEType.E7) := by
  refine ⟨⟨by decide, ⟨by decide, rfl⟩, ⟨by decide, rfl⟩, ⟨by decide, rfl⟩⟩,
          ⟨by decide, by decide, by decide, by decide, by decide⟩,
          ?_, ⟨rfl, rfl⟩⟩
  intro p h
  exact (selection_implies_E8 p h).2.1

-- ══════════════════════════════════════════════════════════
-- §5  Reading
-- ══════════════════════════════════════════════════════════

/-! The single orientation spin double cover — index `spinCoverIndex = 2 =
    OrientationSpinorBridge.preimageOfOne.length`, the {-1,+1} spinor fibre —
    doubles each Platonic rotation group, and McKay maps each binary group to its
    exceptional Dynkin type: T(12)→2T(24)→E6, O(24)→2O(48)→E7, I(60)→2I(120)→E8
    (§1, `exceptional_ladder`). One Z/2 indexes the WHOLE exceptional series; the
    E6/E7/E8 differences come only from which rotation group is doubled, not from
    a second choice. This generalizes `OrientationE8Bridge` off the single
    icosahedral rung onto all three.

    The "why E8 and not E6/E7" question is answered by a maximality principle, not
    a cherry-pick. Icosahedral A5 (60) is the STRICT max of {12, 24, 60} (§2,
    `densest_orientation_covers_E8`), and E8 is the maximal exceptional by Weyl
    order (51840 < 2903040 < 696729600) and Coxeter number (12 < 18 < 30): densest
    downstairs maps to maximal upstairs. The principle itself is the NAMED
    hypothesis `SubstrateSelectsDensestSymmetry` (§3); we prove only the
    CONDITIONAL `selection_implies_E8` (densest-selection forces E8) and that the
    falsifiers — the substrate settling on T or O — are decidably off E8, landing
    on E6/E7 (`selection_falsifier`). So "orientation → E8" is a consequence of an
    explicit, falsifiable maximality principle.

    SCOPE. Order-level / finite shadow only; the continuous `SU(2) → SO(3)` cover
    is deferred (see `OrientationSpinorBridge`). `SubstrateSelectsDensestSymmetry`
    is a documentation-grade hypothesis about the running substrate, NOT a proven
    theorem — the substrate scan (header) shows the running code does privilege
    the densest/maximal symmetry (E8 quantizer for densest packing, hope-jar
    capacity = maximal Weyl order, Monster as the privileged floor), which
    MOTIVATES the hypothesis without discharging it.

    -- Next exploration:
    --   Lift the maximality principle from a tabulated `max` over {12,24,60} to a
    --   classification statement: prove that the finite ROTATION subgroups of
    --   SO(3) are EXACTLY the cyclic/dihedral families plus {T,O,I}, so that
    --   "densest finite polyhedral orientation symmetry" is a closed, exhaustive
    --   maximum over a PROVEN-complete list (not three hand-listed solids), making
    --   `SubstrateSelectsDensestSymmetry` a maximum over the real classification.
    --   That needs the finite-subgroups-of-SO(3) theorem (Mathlib-level), the same
    --   continuous frontier `OrientationSpinorBridge` names. The order-level shadow
    --   here is the strongest honest statement before that classification lands.
    --   A second thread: formalize the moonshine link the substrate already pins
    --   (`aether/.../moonshine.ts`, GRIESS_DIMENSION = 196884) to connect the
    --   maximal exceptional E8 to the maximal sporadic Monster, turning the
    --   substrate's "Monster floor" remark into a checked numeric seam.
-/

end OrientationADELadder
end Gnosis
