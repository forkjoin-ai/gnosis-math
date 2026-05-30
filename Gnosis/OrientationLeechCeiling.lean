/-
  OrientationLeechCeiling
  =======================

  The MOONSHINE TOWER above the orientation sandwich's E8 ceiling.

  `OrientationSandwichBound` pins the orientation / spinor / E8 theory between a
  FLOOR (spin double-cover index 2) and a CEILING (the dimension-8 kissing number
  240 = `kissingCeiling` = E8 root count). Its companion metric doc records

      PREDICTION P3 (docs/orientation-sandwich-metric.md §2.3):
        the 240 ceiling is DIMENSION-8-specific. A quantizer built on the 24-D
        Leech layer would have ceiling 196560, and a Monster-scale layer 196884.

  This module formalizes that P3 ascent as a DECIDABLE DIMENSIONAL CEILING TOWER.
  The E8 ceiling 240 is re-read as the BOTTOM (dim-8 floor) of a higher tower

      240  (E8,   dim 8)   <   196560  (Leech, dim 24)   ≤   196884  (Monster / Griess),

  with the dimension ladder 8 → 24 (24 = 3·8) and the moonshine link to the
  Griess algebra. Each rung is the optimal / maximal object at its level.

  ──────────────────────────────────────────────────────────────────
  WHAT IS PROVED (all by KERNEL `decide`/`rfl`, Init-only):

    1. KISSING-NUMBER TOWER.  240 < 196560, with the carrier dimensions 8 < 24
       and 24 = 3·8. 240 (`E8`) and 196560 (`Leech`) are the optimal kissing
       numbers in dimensions 8 and 24 — named constants, CITED as proven-optimal
       (Viazovska 2016; Cohn–Kumar–Miller–Radchenko–Viazovska 2017).

    2. MONSTER LINK.  The Griess-algebra dimension 196884 decomposes two ways:
         (i)  196884 = 196560 + 324      (Leech-kissing echo; 324 = 18²)
         (ii) 196884 = 196883 + 1        (McKay: smallest faithful Monster
                                          irrep + the trivial rep).
       Both proven as decidable Nat equalities; the moonshine / representation-
       theoretic significance is CITED, not proven.

    3. `leech_ceiling_tower` MASTER.  The ascending chain
         floor 2  ≤  E8 240  ≤  Leech 196560  ≤  Monster/Griess 196884,
       with the dimension ladder 8 → 24 and the role of each rung as the
       optimal/maximal object at its level — read as: the orientation sandwich's
       E8 ceiling 240 is itself the dim-8 FLOOR of a higher moonshine tower that
       tops out (in the substrate's `GRIESS_DIMENSION = 196884`) at the Monster.

  ──────────────────────────────────────────────────────────────────
  HONESTY (over coverage).  We prove ONLY the decidable order / arithmetic facts:
  the inequalities 2 ≤ 240 ≤ 196560 ≤ 196884, the squares-and-sums decompositions
  196560 + 324 = 196884 and 196883 + 1 = 196884 and 324 = 18², and the dimension
  count 24 = 3·8. The DEEP claims are CITED as named obligations, never proven,
  never stated as "X is Y":

    (O1) [E8/Leech optimality]   240 and 196560 are the *optimal* kissing numbers
         in dims 8 and 24 (Viazovska 2016; CKMRV 2017). Needs the magic functions
         / LP bound — NOT formalized here.
    (O2) [Leech structure]       the Leech lattice's 196560 minimal vectors, even
         unimodularity in rank 24, rootlessness, the E8³ Niemeier glue. We prove
         only `24 = 3·8` and cite 196560.
    (O3) [Monster / moonshine]   the Monster sporadic group, its 196883-dim
         irrep, the Griess algebra of dim 196884, and the graded moonshine module
         V♮ with dim Vₙ = c(n). We prove only the Nat arithmetic of the
         coefficients.
    (O4) [324's exact role]      324 = 18² is the residual Eisenstein-correction
         term in `c(1) = (Leech theta) + correction`. We assert the SQUARE
         `324 = 18²` and the SUM `196560 + 324 = 196884` decidably; we do NOT
         claim 324 *counts* a specific moonshine multiplicity here.

  REUSE.  No constant is re-derived. The whole tower is sourced from
  `E8LeechMonsterTower` (`e8RootCount = 240`, `leechKissingNumber = 196560`,
  `monsterFloor = monsterSmallestIrrep + trivialRep = 196884`, `leechDim = 24`,
  `e8Rank = 8`, `niemeierE8Copies = 3`) and the floor `2` from
  `OrientationSandwichBound.floorIndex`. The substrate's `GRIESS_DIMENSION`
  (open-source/aether/src/engine/moonshine.ts) is the runtime mirror of 196884.

  AXIOM HYGIENE.  Every theorem closes by KERNEL `decide`/`rfl` — never
  `native_decide`, no `sorry`, no new `axiom`, no `Classical.choice`. The
  footprint is `propext`-at-most. Verify with `#print axioms leech_ceiling_tower`.
-/

import Gnosis.OrientationSandwichBound
import Gnosis.E8LeechMonsterTower

set_option maxRecDepth 4000

namespace Gnosis
namespace OrientationLeechCeiling

open E8LeechMonsterTower
  (e8RootCount e8Rank leechKissingNumber leechDim niemeierE8Copies
   monsterFloor monsterSmallestIrrep trivialRep jCoeff1)

-- ══════════════════════════════════════════════════════════
-- §0  The four tower rungs, named once from the certs
-- ══════════════════════════════════════════════════════════

/-! Each rung is sourced from an already-proven module; nothing here re-derives a
    value. We name the four levels of the moonshine ceiling tower and the two
    carrier dimensions, then prove the ascending order/arithmetic facts. -/

/-- **FLOOR.** The orientation sandwich's spin double-cover floor index `2`
    (`OrientationSandwichBound.floorIndex`). The very bottom of the whole tower. -/
def floorIndex : Nat := OrientationSandwichBound.floorIndex

/-- **RUNG 1 — E8 ceiling (dim 8).** The 8-dimensional optimal kissing number
    `240`, the E8 root count (`E8LeechMonsterTower.e8RootCount`). The CEILING of
    `OrientationSandwichBound`, re-read here as the dim-8 FLOOR of the tower.
    Optimal in dim 8 by Viazovska 2016 (obligation O1, cited). -/
def e8Ceiling : Nat := e8RootCount

/-- **RUNG 2 — Leech ceiling (dim 24).** The 24-dimensional optimal kissing
    number `196560`, the Leech lattice's minimal-vector count
    (`E8LeechMonsterTower.leechKissingNumber`). Optimal in dim 24 by
    Cohn–Kumar–Miller–Radchenko–Viazovska 2017 (obligation O1, cited). -/
def leechCeiling : Nat := leechKissingNumber

/-- **RUNG 3 — Monster / Griess top.** The Griess-algebra dimension `196884`,
    the q¹-coefficient `c(1)` of the Klein j-invariant and the substrate's
    `GRIESS_DIMENSION` (`E8LeechMonsterTower.monsterFloor`). The moonshine top of
    the tower (obligation O3, cited). -/
def monsterGriess : Nat := monsterFloor

/-- Carrier dimension of the E8 rung: `8`. -/
def e8CarrierDim : Nat := e8Rank

/-- Carrier dimension of the Leech rung: `24`. -/
def leechCarrierDim : Nat := leechDim

/-- The residual term in `c(1) = (Leech kissing) + 324`, stated as the decidable
    square `324 = 18²` (obligation O4 — its exact moonshine role is cited, not
    claimed here). -/
def residual324 : Nat := 324

theorem floor_eq_two       : floorIndex   = 2      := by decide
theorem e8_ceiling_240     : e8Ceiling    = 240    := by decide
theorem leech_ceiling_eq   : leechCeiling = 196560 := by decide
theorem monster_griess_eq  : monsterGriess = 196884 := by decide

/-- The E8 rung agrees with the `OrientationSandwichBound` kissing ceiling — the
    SAME 240. The tower's bottom rung is exactly the lower module's top. -/
theorem e8_rung_is_sandwich_ceiling :
    e8Ceiling = OrientationSandwichBound.kissingCeiling
  ∧ e8Ceiling = E8Lattice.e8Roots.length := by
  refine ⟨by decide, by decide⟩

/-- The Monster top agrees with the j-invariant coefficient `c(1)` and with the
    substrate's `GRIESS_DIMENSION = 196884` (cross-module SSOT). -/
theorem monster_top_is_jcoeff1 :
    monsterGriess = jCoeff1 ∧ monsterGriess = 196884 := by
  refine ⟨by decide, by decide⟩

-- ══════════════════════════════════════════════════════════
-- §1  THE KISSING-NUMBER TOWER — 240 (dim 8) < 196560 (dim 24)
-- ══════════════════════════════════════════════════════════

/-! The two optimal kissing numbers strictly ascend with their carrier
    dimensions: 240 in dim 8, 196560 in dim 24, and 24 = 3·8. The optimality of
    each (obligation O1) is cited, not proven; we prove the order and the
    dimensional arithmetic. -/

/-- **`kissing_tower_strict`.** The optimal kissing numbers strictly ascend from
    the E8 rung to the Leech rung: `240 < 196560`. -/
theorem kissing_tower_strict : e8Ceiling < leechCeiling := by decide

/-- **`carrier_dimension_ladder`.** The carrier dimensions ascend `8 < 24`, and
    the Leech dimension is three times the E8 dimension: `24 = 3·8`. (Reuses
    `E8LeechMonsterTower.leech_dim_is_three_e8`; the lattice isomorphism E8³ ≅
    Niemeier is obligation O2, cited.) -/
theorem carrier_dimension_ladder :
    e8CarrierDim < leechCarrierDim
  ∧ leechCarrierDim = niemeierE8Copies * e8CarrierDim
  ∧ e8CarrierDim = 8
  ∧ leechCarrierDim = 24
  ∧ niemeierE8Copies = 3 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide⟩

/-- **`kissing_numbers_named`.** The two rungs are the named optimal kissing
    numbers of their dimensions: 240 in dim 8 (E8), 196560 in dim 24 (Leech).
    Stated as the equalities of the constants with their dimensions paired; the
    OPTIMALITY (O1) is the cited obligation, not proven here. -/
theorem kissing_numbers_named :
    (e8Ceiling = 240 ∧ e8CarrierDim = 8)
  ∧ (leechCeiling = 196560 ∧ leechCarrierDim = 24)
  ∧ e8Ceiling < leechCeiling := by
  refine ⟨⟨by decide, by decide⟩, ⟨by decide, by decide⟩, by decide⟩

-- ══════════════════════════════════════════════════════════
-- §2  THE MONSTER LINK — 196884 = 196560 + 324 = 196883 + 1
-- ══════════════════════════════════════════════════════════

/-! The Griess dimension 196884 sits just above the Leech kissing number and is
    the moonshine top. Two decidable decompositions: the Leech-kissing echo
    (+324 = +18²) and McKay's relation (196883 + 1). The representation theory
    these shadow is obligation O3 (cited). -/

/-- **`residual_is_eighteen_squared`.** The residual term is the perfect square
    `324 = 18²`. (Obligation O4: its exact moonshine multiplicity role is cited,
    not claimed; we assert only the decidable square.) -/
theorem residual_is_eighteen_squared :
    residual324 = 18 * 18 ∧ residual324 = 324 := by
  refine ⟨by decide, by decide⟩

/-- **`monster_leech_echo`.** The moonshine top decomposes as the Leech kissing
    number plus the residual square: `196884 = 196560 + 324`, with `324 = 18²`.
    (Reuses `E8LeechMonsterTower.monster_floor_leech_echo`.) A genuine arithmetic
    echo of the Leech theta series inside `c(1)`. -/
theorem monster_leech_echo :
    monsterGriess = leechCeiling + residual324
  ∧ residual324 = 18 * 18
  ∧ leechCeiling + 324 = 196884 := by
  refine ⟨by decide, by decide, by decide⟩

/-- **`monster_mckay_relation`.** McKay's 1978 moonshine observation: the
    moonshine top decomposes as the smallest faithful irreducible representation
    of the Monster plus the trivial representation: `196884 = 196883 + 1`.
    (Reuses `E8LeechMonsterTower.mckay_relation`; the Monster irrep is obligation
    O3, cited.) -/
theorem monster_mckay_relation :
    monsterGriess = monsterSmallestIrrep + trivialRep
  ∧ monsterSmallestIrrep = 196883
  ∧ trivialRep = 1
  ∧ monsterSmallestIrrep + 1 = 196884 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- **`monster_two_decompositions`.** The Griess dimension viewed two ways at
    once — the Leech-kissing echo and McKay's relation agree on `196884`:
        196560 + 324  =  196884  =  196883 + 1,
    so `196560 + 324 = 196883 + 1`. Both are decidable Nat identities; the deep
    moonshine identity they shadow (O3) is cited. -/
theorem monster_two_decompositions :
    leechCeiling + residual324 = monsterGriess
  ∧ monsterSmallestIrrep + trivialRep = monsterGriess
  ∧ leechCeiling + residual324 = monsterSmallestIrrep + trivialRep := by
  refine ⟨by decide, by decide, by decide⟩

/-- **`monster_above_leech`.** The moonshine top sits strictly above the Leech
    kissing number, by exactly the residual square: `196560 < 196884` and
    `196884 - 196560 = 324 = 18²`. -/
theorem monster_above_leech :
    leechCeiling < monsterGriess
  ∧ monsterGriess - leechCeiling = residual324
  ∧ monsterGriess - leechCeiling = 18 * 18 := by
  refine ⟨by decide, by decide, by decide⟩

-- ══════════════════════════════════════════════════════════
-- §3  leech_ceiling_tower — floor 2 ≤ E8 240 ≤ Leech 196560 ≤ Monster 196884
-- ══════════════════════════════════════════════════════════

/-! The full ascending chain in one certificate, tying the orientation floor, the
    E8 dim-8 ceiling, the Leech dim-24 ceiling, and the Monster/Griess top into a
    single decidable tower, with the dimension ladder 8 → 24. -/

/-- **`tower_ascending_chain`.** The four rungs strictly/weakly ascend as a chain:
        floor 2  <  E8 240  <  Leech 196560  <  Monster 196884.
    (All four `<`; the wider `≤` framing of the master uses these.) -/
theorem tower_ascending_chain :
    floorIndex < e8Ceiling
  ∧ e8Ceiling < leechCeiling
  ∧ leechCeiling < monsterGriess := by
  refine ⟨by decide, by decide, by decide⟩

/-- **`leech_ceiling_tower` — the MOONSHINE CEILING TOWER, one certificate.**

    Bundles §1–§2 into a single kernel-decidable ascending tower above the
    orientation sandwich's E8 ceiling:

      (BOTTOM / sandwich seam)
        floorIndex = 2 (the spin double-cover floor) and the E8 rung 240 is
        exactly `OrientationSandwichBound.kissingCeiling` — the lower module's
        CEILING is this tower's dim-8 FLOOR.

      (KISSING TOWER, §1)
        E8 240 (dim 8)  <  Leech 196560 (dim 24),  with 8 < 24 and 24 = 3·8.
        Each is the optimal kissing number of its dimension (obligation O1,
        cited: Viazovska 2016; CKMRV 2017).

      (MONSTER LINK, §2)
        Leech 196560  <  Monster/Griess 196884, with
            196884 = 196560 + 324  (324 = 18²)   and   196884 = 196883 + 1
        (McKay; the Monster irrep / Griess algebra / moonshine module are
        obligations O2–O3, cited).

      (THE ASCENDING CHAIN)
        floor 2  ≤  E8 240  ≤  Leech 196560  ≤  Monster 196884,
        each `≤` a kernel-checked decidable order fact.

    Read as one line: the orientation sandwich's E8 ceiling (240, dim 8) is the
    FLOOR of a higher moonshine tower whose dim-24 rung is the Leech kissing
    number 196560 and whose top, in the substrate's `GRIESS_DIMENSION`, is the
    Monster/Griess 196884. -/
theorem leech_ceiling_tower :
    -- ── BOTTOM / sandwich seam ────────────────────────────────
    ( floorIndex = 2
      ∧ e8Ceiling = OrientationSandwichBound.kissingCeiling
      ∧ e8Ceiling = 240 )
    -- ── KISSING TOWER (§1): E8 dim 8 < Leech dim 24, 24 = 3·8 ──
  ∧ ( e8Ceiling < leechCeiling
      ∧ e8CarrierDim < leechCarrierDim
      ∧ leechCarrierDim = niemeierE8Copies * e8CarrierDim
      ∧ e8CarrierDim = 8
      ∧ leechCarrierDim = 24
      ∧ leechCeiling = 196560 )
    -- ── MONSTER LINK (§2): 196884 = 196560+324 = 196883+1 ──────
  ∧ ( leechCeiling < monsterGriess
      ∧ monsterGriess = leechCeiling + residual324
      ∧ residual324 = 18 * 18
      ∧ monsterGriess = monsterSmallestIrrep + trivialRep
      ∧ monsterGriess = 196884 )
    -- ── THE ASCENDING CHAIN: 2 ≤ 240 ≤ 196560 ≤ 196884 ─────────
  ∧ ( floorIndex   ≤ e8Ceiling      -- 2 ≤ 240
      ∧ e8Ceiling   ≤ leechCeiling   -- 240 ≤ 196560
      ∧ leechCeiling ≤ monsterGriess -- 196560 ≤ 196884
      -- and the chain is strict at every step
      ∧ floorIndex < e8Ceiling
      ∧ e8Ceiling < leechCeiling
      ∧ leechCeiling < monsterGriess )
:= by
  refine ⟨⟨by decide, by decide, by decide⟩,
          ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩,
          ⟨by decide, by decide, by decide, by decide, by decide⟩,
          ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩⟩

-- ══════════════════════════════════════════════════════════
-- §4  SCOPE  (honesty over coverage) — the cited obligations
-- ══════════════════════════════════════════════════════════
/--
  `deferred_scope` — a trivially-true marker whose docstring is the honest scope
  statement (kept in the kernel as `True`, part of the compiled artifact).

  PROVED HERE (all by kernel `decide`/`rfl`, Init-only):
    • 240 < 196560              E8 (dim 8) kissing < Leech (dim 24) kissing
    • 8 < 24, 24 = 3·8          carrier-dimension ladder
    • 324 = 18²                 the residual square
    • 196884 = 196560 + 324     Leech-kissing echo in c(1)
    • 196884 = 196883 + 1       McKay's relation
    • 196560 + 324 = 196883 + 1 the two decompositions agree
    • 2 ≤ 240 ≤ 196560 ≤ 196884  the full ascending tower (strict at each step)

  CITED OBLIGATIONS (NOT proven — far beyond Init):
    (O1) [optimality]  240 and 196560 are the OPTIMAL kissing numbers in dims 8
         and 24 (Viazovska 2016; Cohn–Kumar–Miller–Radchenko–Viazovska 2017).
         Needs the magic modular functions / LP bound. We cite; we prove only
         the order 240 < 196560.
    (O2) [Leech structure]  the Leech lattice (196560 minimal vectors, even
         unimodular rank 24, rootless, the E8³ Niemeier glue / isomorphism). We
         prove only `24 = 3·8` and cite 196560.
    (O3) [Monster / moonshine]  the Monster sporadic simple group, its
         196883-dim faithful irrep, the Griess algebra of dim 196884, and the
         graded moonshine module V♮ with dim Vₙ = c(n) (Conway–Norton; Borcherds
         1992). We prove only the Nat coefficient arithmetic.
    (O4) [324's exact role]  324 = 18² is the residual Eisenstein-correction term
         in `c(1) = (Leech theta) + correction`. We assert the SQUARE and the SUM
         decidably; we do NOT claim 324 counts a specific moonshine multiplicity.

  These shadows are TRUE and DECIDABLE; the structures they shadow are deferred
  honestly, exactly as `E8LeechMonsterTower` / `OrientationSandwichBound` defer
  the lattice / group / continuous pieces. No "X is Y" identity is manufactured.
-/
theorem deferred_scope : True := trivial

#print axioms leech_ceiling_tower

end OrientationLeechCeiling
end Gnosis
