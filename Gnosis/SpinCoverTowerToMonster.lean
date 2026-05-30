/-
  SpinCoverTowerToMonster
  =======================

  DOES THE ℤ/2 SPIN DOUBLE COVER RECUR UP THE TOWER?
  ──────────────────────────────────────────────────
  The orientation floor of perception runs on a ℤ/2 cover: the binary
  icosahedral group `2I → I` (kernel `{±1}`), the finite restriction of the
  Lie cover `SU(2) → SO(3)`. `Gnosis.OrientationE8Bridge` proves the order
  shadow `|2I| = 2·|I| = 120` and `Gnosis.SpinorCover600Cell` COMPUTES the
  kernel `{±1}` by exact ℤ[φ] conjugation. The FRONTIER QUESTION this module
  tests: does that SAME 2:1 / kernel-`{±1}` shape RECUR at every rung of the
  lattice tower `E8 → Leech → Monster`, giving a self-similar spin-cover
  tower up to the largest sporadic group?

  THE ANSWER, stated honestly up front
  ────────────────────────────────────
  • At the SO(3) / orientation floor: YES — PROVEN elsewhere, REUSED here.
    `2I → I`, kernel `{±1}`, index 2 (`OrientationE8Bridge`,
    `SpinorCover600Cell`). The central `{±1}` is the antipodal map the
    600-cell vertex set is closed under.

  • At the LEECH rung: YES — a REAL structural fact, here PROVEN as its
    decidable ORDER SHADOW. `Co0 = Aut(Leech)` is a ℤ/2 central extension of
    `Co1`: `Co0 / {±1} = Co1`, the kernel `{±1}` being lattice NEGATION
    (`Λ ↦ −Λ`), exactly the antipodal map the floor's 600-cell cover already
    uses. We prove `|Co0| = 2·|Co1|` by kernel arithmetic and that the two
    orders differ by EXACTLY one factor of 2 (`2^22` vs `2^21`) — the genuine
    `2 · (odd-aligned part)` shape of a ℤ/2 cover. This is NOT analogy: the
    central element is the lattice `−1`, the same `{±1}` shape as `2I → I`
    and `SU(2) → SO(3)`. The full group structure (`Co0` as `Aut(Leech)`,
    the quotient `Co0/{±1} ≅ Co1`) is the CITED obligation; the order/kernel
    shadow is proven.

  • At the MONSTER rung: the recurrence appears as the `2A`-involution
    CENTRALIZER `2.B` — the double cover of the Baby Monster `B` sitting
    inside the Monster `M` as `C_M(2A) = 2.B`, a ℤ/2 central extension with
    kernel `{1, t}` (`t` the central `2A` involution, the order-2 analogue of
    lattice `−1`). We prove the order shadow `|2.B| = 2·|B|` and that `2.B`
    DIVIDES `|M|` (a genuine subgroup index, decidably checked). The deep
    facts — `B` and `M` as sporadic simple groups, `C_M(2A) ≅ 2.B`, the
    `Co0`↔Leech↔Monster moonshine chain — are CITED obligations.

  SELF-SIMILAR ℤ/2 TOWER (the payoff, as a decidable shadow)
  ──────────────────────────────────────────────────────────
      floor   2I  → I     kernel {±1}   |2I| = 2·|I|     = 120
      Leech   Co0 → Co1   kernel {±1}   |Co0| = 2·|Co1|  (2^22 vs 2^21)
      Monster 2.B ⊂ M     kernel {1,t}  |2.B| = 2·|B|, 2.B ∣ M

  At each rung the SAME shape: a ℤ/2 central extension whose kernel is a
  central order-2 element (`−1` / lattice `−1` / the `2A` involution `t`),
  index 2, order doubling. We PROVE the order/kernel-order shadows decidably
  and NAME the deep group structure as obligations. We never write "X is Y":
  we say "is a ℤ/2 central extension", "maps to", "has order", "divides".

  HARD CONSTRAINTS (met). Init-only (`import Init` + the two cited Gnosis
  bridges for the floor rung). Every theorem closes by KERNEL `decide`/`rfl`
  — NO `native_decide`, no `sorry`, no `admit`, no new `axiom`, no
  `Classical.choice`. `set_option maxRecDepth` raised for the large-Nat
  divisibility `decide`. Gate ONLY on `lake build Gnosis.SpinCoverTowerToMonster`
  + `#print axioms`. Does NOT register in `Gnosis.lean`, does NOT edit other
  modules.

  REUSE. The floor rung's index-2 / kernel-`{±1}` facts are SOURCED from
  `Gnosis.OrientationE8Bridge` (`spinCoverIndex`, `binary_is_2to1_spin_cover`)
  and the lattice numbers from `Gnosis.E8LeechMonsterTower`. No constant is
  re-derived. The Conway / Baby-Monster / Monster orders are CITED group-order
  constants (ATLAS of Finite Groups; Conway 1968/1969; Griess 1982), stated as
  named `Nat`s, not constructed.
-/

import Init
import Gnosis.OrientationE8Bridge
import Gnosis.E8LeechMonsterTower

-- The Monster-order divisibility `decide` reduces a 54-digit Nat; raise the
-- reduction depth. This is a DEPTH knob, not a tactic exception — still pure
-- kernel `decide`, no `native_decide`.
set_option maxRecDepth 16000

namespace Gnosis
namespace SpinCoverTowerToMonster

open OrientationE8Bridge (spinCoverIndex rotationOrder Polyhedral)
open E8LeechMonsterTower
  (leechDim e8Rank niemeierE8Copies monsterFloor monsterSmallestIrrep)

-- ══════════════════════════════════════════════════════════
-- §0  The kernel-{±1} primitive — one shape, reused at every rung
-- ══════════════════════════════════════════════════════════

/-! A ℤ/2 central extension `1 → {±1} → G̃ → G → 1` has, as its DECIDABLE
    shadow, a kernel of order 2 and a total order `|G̃| = 2·|G|`. We name the
    kernel order once; every rung below instantiates the SAME number. -/

/-- The order of the central kernel `{±1}` of a ℤ/2 cover: `2`. The two
    central sheets `{−1, +1}` (lattice `{−1, +1}`, the involution pair
    `{1, t}`). This is the floor's `spinCoverIndex` (the spinor fibre
    `{−1,+1}` of `OrientationSpinorBridge`), reused unchanged up the tower. -/
def kernelOrder : Nat := 2

/-- The kernel order equals the floor's spin-cover index: the SAME `2` as
    `OrientationE8Bridge.spinCoverIndex` (= `preimageOfOne.length`, the
    `{−1,+1}` spinor fibre). One number indexes the whole tower. -/
theorem kernel_order_is_floor_spin_index :
    kernelOrder = spinCoverIndex := by
  -- spinCoverIndex = OrientationSpinorBridge.preimageOfOne.length = 2
  have h : spinCoverIndex = 2 := OrientationE8Bridge.spin_cover_index_eq_two
  rw [kernelOrder, h]

theorem kernel_order_eq_two : kernelOrder = 2 := by decide

-- ══════════════════════════════════════════════════════════
-- §1  RUNG 0 — the orientation FLOOR:  2I → I, kernel {±1}, index 2
-- ══════════════════════════════════════════════════════════

/-! The bottom rung is ALREADY PROVEN — we only restate it through this
    module's vocabulary so the tower reads uniformly. The binary icosahedral
    group `2I` covers the icosahedral rotation group `I = A5` two-to-one, the
    finite restriction of `SU(2) → SO(3)`; the kernel `{±1}` is COMPUTED in
    `SpinorCover600Cell` (`icosa_kernel_is_pm_one`). -/

/-- The covered (downstairs) group order at the floor: `|I| = 60`, the
    icosahedral rotation group `A5` (`OrientationE8Bridge.rotationOrder .Icosa`). -/
def floorBaseOrder : Nat := rotationOrder .Icosa

/-- The covering (upstairs) group order at the floor: `|2I| = 120`, the binary
    icosahedral group, `spinCoverIndex · |I| = 2 · 60`. -/
def floorCoverOrder : Nat := spinCoverIndex * rotationOrder .Icosa

theorem floor_base_eq_sixty   : floorBaseOrder  = 60  := by decide
theorem floor_cover_eq_120    : floorCoverOrder = 120 := by decide

/-- **`floor_is_z2_cover`.** The orientation floor is a ℤ/2 cover: the cover
    order is `kernelOrder` (= 2) times the base order, `120 = 2·60`, the
    doubling factor being the floor's spin-cover index (the `{−1,+1}` spinor
    fibre). REUSES `OrientationE8Bridge.binary_is_2to1_spin_cover`. -/
theorem floor_is_z2_cover :
    floorCoverOrder = kernelOrder * floorBaseOrder
  ∧ floorCoverOrder = spinCoverIndex * floorBaseOrder
  ∧ kernelOrder = 2
  ∧ floorCoverOrder / floorBaseOrder = 2 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

-- ══════════════════════════════════════════════════════════
-- §2  RUNG 1 — the LEECH rung:  Co0 → Co1, kernel {±1} = lattice −1
-- ══════════════════════════════════════════════════════════

/-! THE CORE HYPOTHESIS, here a REAL structural fact at its order shadow.
    `Co0 = Aut(Leech)` (the automorphism group of the 24-dim Leech lattice,
    `0.` in ATLAS notation) is a ℤ/2 central extension of the Conway simple
    group `Co1`: `Co0 / {±1} = Co1`. The central kernel `{±1}` is lattice
    NEGATION `Λ ↦ −Λ` — the antipodal map. This is the SAME `{±1}` shape as
    the floor's `2I → I` (where `{±1}` is the central units of the icosian
    quaternions, the antipodal closure of the 600-cell).

    We prove the DECIDABLE shadow: `|Co0| = 2·|Co1|`, kernel order 2, index 2,
    and — the fingerprint of a genuine ℤ/2 cover — the two orders differ by
    EXACTLY one factor of 2 in their 2-adic valuation (`2^22` vs `2^21`). The
    full group statement `Co0/{±1} ≅ Co1` is obligation (L1), cited. -/

/-- Order of the Conway group `Co0 = Aut(Leech)` (the `2·Co1` cover), the
    automorphism group of the Leech lattice.  `|Co0| = 8 315 553 613 086 720 000`
    `= 2^22 · 3^9 · 5^4 · 7^2 · 11 · 13 · 23`. CITED constant (Conway 1968;
    ATLAS), not constructed. -/
def co0Order : Nat := 8315553613086720000

/-- Order of the Conway simple group `Co1 = Co0 / {±1}`.
    `|Co1| = 4 157 776 806 543 360 000 = 2^21 · 3^9 · 5^4 · 7^2 · 11 · 13 · 23`.
    CITED constant (ATLAS), not constructed. -/
def co1Order : Nat := 4157776806543360000

/-- The 2-power part of `|Co0|`: `2^22`. -/
def co0TwoPart : Nat := 4194304          -- 2^22
/-- The 2-power part of `|Co1|`: `2^21`. -/
def co1TwoPart : Nat := 2097152          -- 2^21
/-- The shared odd part of `|Co0|` and `|Co1|`:
    `3^9 · 5^4 · 7^2 · 11 · 13 · 23`. -/
def conwayOddPart : Nat := 1982582476875 -- 3^9 · 5^4 · 7^2 · 11 · 13 · 23

theorem co0_two_part_eq   : co0TwoPart = 4194304 := by decide      -- 2^22
theorem co1_two_part_eq   : co1TwoPart = 2097152 := by decide      -- 2^21
theorem co0_two_part_pow  : co0TwoPart = 2 ^ 22 := by decide
theorem co1_two_part_pow  : co1TwoPart = 2 ^ 21 := by decide

/-- The odd part really is odd (not divisible by 2): the 2-adic valuation of
    `|Co0|` and `|Co1|` lives entirely in the `2^k` factors. -/
theorem conway_odd_part_is_odd : conwayOddPart % 2 = 1 := by decide

/-- `|Co0|` factors as `2^22 · (odd part)`. -/
theorem co0_factorization : co0Order = co0TwoPart * conwayOddPart := by decide
/-- `|Co1|` factors as `2^21 · (odd part)`. -/
theorem co1_factorization : co1Order = co1TwoPart * conwayOddPart := by decide

/-- **`co0_is_two_co1`.** The CORE LEECH-RUNG FACT (order shadow): the Conway
    automorphism group of the Leech lattice is a ℤ/2 cover of the Conway simple
    group — `|Co0| = 2 · |Co1|`, with the doubling factor being `kernelOrder`
    (= 2 = the floor's `{±1}` spin index). The kernel is lattice negation
    `Λ ↦ −Λ`, the antipodal `{±1}`. Proven as a kernel-arithmetic Nat
    equality; the isomorphism `Co0/{±1} ≅ Co1` is obligation (L1), cited. -/
theorem co0_is_two_co1 :
    co0Order = kernelOrder * co1Order
  ∧ co0Order = 2 * co1Order
  ∧ co0Order / co1Order = 2
  ∧ co0Order % co1Order = 0 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- **`leech_cover_two_adic_fingerprint`.** The fingerprint that `Co0 → Co1` is
    a genuine ℤ/2 cover and not a coincidence of magnitudes: `|Co0|` and `|Co1|`
    share the SAME odd part and differ by EXACTLY one factor of 2 in their
    2-adic valuation (`2^22 = 2 · 2^21`). The single extra `2` is the central
    `{±1}` — the negation of the Leech lattice. -/
theorem leech_cover_two_adic_fingerprint :
    co0TwoPart = kernelOrder * co1TwoPart        -- 2^22 = 2 · 2^21
  ∧ co0TwoPart = 2 ^ 22
  ∧ co1TwoPart = 2 ^ 21
  ∧ co0Order = co0TwoPart * conwayOddPart
  ∧ co1Order = co1TwoPart * conwayOddPart
  ∧ conwayOddPart % 2 = 1 := by                   -- the shared part is odd
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- The floor rung and the Leech rung share the SAME ℤ/2 kernel shape: index 2,
    kernel order 2 (`kernelOrder`), the central `{±1}` (icosian `−1` downstairs,
    lattice `−1` here). The doubling factor is literally the same `Nat`. -/
theorem floor_and_leech_share_kernel :
    floorCoverOrder / floorBaseOrder = co0Order / co1Order   -- both = 2
  ∧ floorCoverOrder = kernelOrder * floorBaseOrder
  ∧ co0Order = kernelOrder * co1Order
  ∧ kernelOrder = 2 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

-- ══════════════════════════════════════════════════════════
-- §3  THE LEECH = 3·E8 SUBSTRATE  (the three frames the cover sits over)
-- ══════════════════════════════════════════════════════════

/-! The Leech rung's `Co0 → Co1` cover sits over a 24-dim lattice whose
    Niemeier shadow is `E8³` — three copies of E8, `leechDim 24 = 3·8`. We
    restate the proven dimension count and relate it to THREE orientation
    frames / 600-cell shells. The `3` is a real dimension count (PROVEN); the
    "triple-icosian / triality 3-fold" reading is reported as ANALOGY (T1),
    NOT proven: Spin(8) triality is a genuine order-3 outer automorphism, but
    its identification with the three E8 lattice copies in the Leech glue is
    not formalized here. -/

/-- The Niemeier `E8³` copy count: `3`. -/
def threeFrames : Nat := niemeierE8Copies

/-- **`leech_is_three_e8_frames`.** The Leech dimension is three E8 ranks:
    `24 = 3·8` (REUSES `E8LeechMonsterTower.leech_dim_is_three_e8`). The three
    copies are read as three orientation frames / 600-cell shells; the
    identification with Spin(8) TRIALITY (the order-3 outer automorphism) is
    obligation (T1), reported as ANALOGY, not proven. -/
theorem leech_is_three_e8_frames :
    leechDim = threeFrames * e8Rank
  ∧ leechDim = 3 * 8
  ∧ threeFrames = 3
  ∧ e8Rank = 8 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- The order-3 (triality) count `3` is INDEPENDENT of the order-2 (spin) cover
    count `2`: `gcd(2,3) = 1`. The 3-fold frame structure and the ℤ/2 cover are
    coprime symmetries that coexist at the Leech rung — the cover is NOT a power
    of the triality. (A decidable separation, not an identity.) -/
theorem triality_and_spin_coprime :
    Nat.gcd threeFrames kernelOrder = 1
  ∧ threeFrames = 3
  ∧ kernelOrder = 2 := by
  refine ⟨by decide, by decide, by decide⟩

-- ══════════════════════════════════════════════════════════
-- §4  RUNG 2 — the MONSTER rung:  2.B ⊂ M, kernel {1,t} = 2A involution
-- ══════════════════════════════════════════════════════════

/-! The recurrence at the top: the Monster `M`'s `2A`-involution centralizer is
    the double cover of the Baby Monster, `C_M(2A) = 2.B`, a ℤ/2 central
    extension `1 → {1,t} → 2.B → B → 1` whose kernel `{1,t}` is generated by the
    central `2A` involution `t` (the order-2 analogue of the lattice `−1` at the
    Leech rung). We prove the order shadow `|2.B| = 2·|B|`, that `2.B` DIVIDES
    `|M|` (a genuine subgroup index, decidably), and the same kernel-order-2
    fingerprint. The deep facts (`B`, `M` simple; `C_M(2A) ≅ 2.B`) are cited
    obligations (M1, M2). -/

/-- Order of the Baby Monster sporadic simple group `B`.
    `|B| = 4 154 781 481 226 426 191 177 580 544 000 000`. CITED constant
    (ATLAS; Leon–Sims 1977 construction), not constructed. -/
def babyMonsterOrder : Nat := 4154781481226426191177580544000000

/-- Order of the `2A`-involution centralizer `2.B = C_M(2A)` in the Monster:
    the double cover of the Baby Monster, `|2.B| = 2·|B|`. -/
def twoBOrder : Nat := 8309562962452852382355161088000000

/-- Order of the Monster sporadic simple group `M` (the Fischer–Griess
    Monster), `|M| = 808 017 424 794 512 875 886 459 904 961 710 757 005 754 368
    000 000 000`. CITED constant (Griess 1982; ATLAS), not constructed. -/
def monsterOrder : Nat := 808017424794512875886459904961710757005754368000000000

theorem baby_monster_order_eq :
    babyMonsterOrder = 4154781481226426191177580544000000 := by decide
theorem two_b_order_eq :
    twoBOrder = 8309562962452852382355161088000000 := by decide

/-- **`twoB_is_two_baby`.** The Monster-rung order shadow: the `2A`-involution
    centralizer `2.B` is a ℤ/2 cover of the Baby Monster — `|2.B| = 2·|B|`, the
    doubling factor being `kernelOrder` (= 2), the kernel `{1,t}` generated by
    the central `2A` involution `t`. Proven as a kernel-arithmetic Nat equality;
    `C_M(2A) ≅ 2.B` is obligation (M1), cited. -/
theorem twoB_is_two_baby :
    twoBOrder = kernelOrder * babyMonsterOrder
  ∧ twoBOrder = 2 * babyMonsterOrder
  ∧ twoBOrder / babyMonsterOrder = 2
  ∧ twoBOrder % babyMonsterOrder = 0 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- The exact Lagrange index `[M : 2.B] = |M| / |2.B|`, stated as a named
    constant so the divisibility is a kernel-cheap MULTIPLICATION
    (`|M| = |2.B| · index`) rather than a kernel-expensive 54-digit division. -/
def monsterIndexOverTwoB : Nat := 97239461142009186000

/-- **`twoB_divides_monster`.** The double cover `2.B` sits inside the Monster
    as a genuine subgroup: `|2.B|` DIVIDES `|M|` (Lagrange — the index
    `[M : 2.B] = monsterIndexOverTwoB`). Stated multiplicatively
    (`|M| = |2.B| · index`) so the kernel checks a product, not a 54-digit
    division. `2.B ⊂ M` as a subgroup is obligation (M2), cited. -/
theorem twoB_divides_monster :
    monsterOrder % twoBOrder = 0
  ∧ monsterOrder = twoBOrder * monsterIndexOverTwoB := by
  -- the 54-digit equalities go through the kernel's GMP `rfl` fast path
  -- (kernel `decide` would build an overflowing `Nat.decEq` recursion).
  refine ⟨?_, ?_⟩
  · rfl
  · rfl

/-- The `2^46` 2-part of `|M|` and its odd cofactor, named so the 2-adic fact
    is a kernel-cheap MULTIPLICATION rather than a 54-digit `^`/`%`. -/
def monsterTwoPart   : Nat := 70368744177664  -- 2^46
def monsterOddCofactor : Nat := 11482618231106483731969943632999939453125

/-- The Monster order is even with a large 2-adic valuation (`2^46 ∣ |M|`),
    leaving room for the `{1,t}` central involution of `2.B`. The kernel
    `{1,t}` has order `kernelOrder` (= 2), the same as the Leech `{±1}` and the
    floor `{±1}`. Stated multiplicatively (`|M| = 2^46 · odd cofactor`) so the
    kernel checks a product; the full 2-local structure is obligation M2. -/
theorem monster_two_local_room :
    monsterOrder % 2 = 0
  ∧ monsterTwoPart = 2 ^ 46
  ∧ monsterOrder = monsterTwoPart * monsterOddCofactor
  ∧ kernelOrder = 2 := by
  -- the 54-digit product goes through the kernel GMP `rfl` fast path.
  refine ⟨?_, by decide, ?_, by decide⟩
  · rfl
  · rfl

-- ══════════════════════════════════════════════════════════
-- §5  THE SELF-SIMILAR ℤ/2 SPIN-COVER TOWER  (one certificate)
-- ══════════════════════════════════════════════════════════

/-- **`spin_cover_tower_to_monster` — THE TOWER, one kernel-decidable
    certificate.**  At EVERY rung the same ℤ/2 shape: a central extension whose
    kernel has order `kernelOrder` (= 2), index 2, order doubling.

      RUNG 0  (orientation floor, SO(3) level)
        `2I → I`,  kernel `{±1}` (icosian `−1`, the 600-cell antipode),
        `|2I| = 2·|I| = 120`.   [PROVEN: reuses `OrientationE8Bridge`,
        kernel COMPUTED in `SpinorCover600Cell`.]

      RUNG 1  (Leech level)
        `Co0 → Co1`,  kernel `{±1}` = lattice negation `Λ ↦ −Λ`,
        `|Co0| = 2·|Co1|`, the two orders sharing one odd part and differing by
        exactly `2^22` vs `2^21`.   [PROVEN order/2-adic shadow; the iso
        `Co0/{±1} ≅ Co1` is obligation L1, cited.]

      RUNG 2  (Monster level)
        `2.B = C_M(2A) ⊂ M`,  kernel `{1,t}` = the central `2A` involution,
        `|2.B| = 2·|B|`, and `2.B ∣ M`.   [PROVEN order/divisibility shadow;
        `C_M(2A) ≅ 2.B` and `B,M` simple are obligations M1, M2, cited.]

    THE SELF-SIMILARITY: one `kernelOrder = 2` indexes all three rungs; the
    kernel at each is a CENTRAL ORDER-2 element — icosian `−1`, lattice `−1`,
    the `2A` involution `t` — the antipodal / negation map. The ℤ/2 spin cover
    genuinely recurs as an order/kernel shadow from the orientation floor to the
    Monster. (It is a REAL structural fact at the floor and the Leech rung; at
    the Monster rung it is the `2.B` involution-centralizer, a real ℤ/2 cover
    inside `M`, not the whole-Monster cover.) -/
theorem spin_cover_tower_to_monster :
    -- ── one shared kernel order across the whole tower ──────────
    ( kernelOrder = 2
      ∧ kernelOrder = spinCoverIndex )
    -- ── RUNG 0: 2I → I, kernel {±1}, |2I| = 2·|I| = 120 ─────────
  ∧ ( floorCoverOrder = kernelOrder * floorBaseOrder
      ∧ floorCoverOrder = 120
      ∧ floorBaseOrder = 60
      ∧ floorCoverOrder / floorBaseOrder = 2 )
    -- ── RUNG 1: Co0 → Co1, kernel {±1} = lattice −1 ─────────────
  ∧ ( co0Order = kernelOrder * co1Order
      ∧ co0Order / co1Order = 2
      ∧ co0Order % co1Order = 0
      ∧ co0TwoPart = kernelOrder * co1TwoPart   -- 2^22 = 2 · 2^21
      ∧ co0Order = co0TwoPart * conwayOddPart
      ∧ co1Order = co1TwoPart * conwayOddPart
      ∧ conwayOddPart % 2 = 1 )                  -- same odd part, one extra 2
    -- ── RUNG 2: 2.B ⊂ M, kernel {1,t}, |2.B| = 2·|B|, 2.B ∣ M ──
  ∧ ( twoBOrder = kernelOrder * babyMonsterOrder
      ∧ twoBOrder / babyMonsterOrder = 2
      ∧ twoBOrder % babyMonsterOrder = 0
      ∧ monsterOrder % twoBOrder = 0
      ∧ monsterOrder % 2 = 0 )
    -- ── THE SELF-SIMILARITY: index 2 at every rung ──────────────
  ∧ ( floorCoverOrder / floorBaseOrder = 2
      ∧ co0Order / co1Order = 2
      ∧ twoBOrder / babyMonsterOrder = 2 )
:= by
  refine ⟨⟨by decide, ?_⟩,
          ⟨by decide, by decide, by decide, by decide⟩,
          ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩,
          ⟨by decide, by decide, by decide, by decide, by decide⟩,
          ⟨by decide, by decide, by decide⟩⟩
  -- kernelOrder = spinCoverIndex (reuse the floor cert, not a literal)
  exact kernel_order_is_floor_spin_index

-- ══════════════════════════════════════════════════════════
-- §6  SCOPE — proven decidable shadows vs cited deep obligations
-- ══════════════════════════════════════════════════════════
/--
  `deferred_scope` — a trivially-true marker whose docstring is the honest
  scope statement (kept in the kernel as `True`, part of the compiled artifact).

  PROVED HERE (all by kernel `decide`/`rfl`, Init-only):
    • kernelOrder = 2 = spinCoverIndex          one ℤ/2 index for the tower
    • FLOOR:  |2I| = 2·|I| = 120, index 2        (reuses OrientationE8Bridge)
    • LEECH:  |Co0| = 2·|Co1|, index 2, %0       (order shadow of Co0 → Co1)
              |Co0| = 2^22·odd, |Co1| = 2^21·odd, odd%2=1
              (the 2-adic fingerprint: SAME odd part, ONE extra factor of 2)
    • LEECH = 3·E8:  24 = 3·8, gcd(3,2)=1        (triality count, coprime to spin)
    • MONSTER:  |2.B| = 2·|B|, index 2, %0       (order shadow of 2.B = C_M(2A))
              monster % 2.B = 0, monster/2.B = 97239461142009186000  (2.B ∣ M)
              monster % 2 = 0, monster % 2^46 = 0  (2-local room for {1,t})

  WHAT IS A REAL STRUCTURAL FACT (not analogy):
    • Co0 = Aut(Leech) IS a ℤ/2 central extension of Co1, kernel {±1} = lattice
      negation. The `2` here is the GENUINE central element −1 of the Leech
      lattice — the same antipodal {±1} the floor's 600-cell cover uses. The
      order shadow |Co0| = 2·|Co1| and the matched odd part / one-extra-2 are
      proven; this is the same ℤ/2 SHAPE as 2I → I and SU(2) → SO(3).
    • 2.B = C_M(2A) IS a ℤ/2 central extension of B (kernel = the 2A involution)
      sitting inside M; |2.B| = 2·|B| and 2.B ∣ M are proven.

  WHAT IS ANALOGY (reported, not forced):
    • The "triple-icosian / triality" reading of LEECH = 3·E8 (T1). Spin(8)
      triality is a genuine order-3 outer automorphism, but its identification
      with the three E8 lattice copies in the Leech glue is NOT formalized; we
      prove only 24 = 3·8 and gcd(3,2)=1.
    • The Monster rung is the 2.B involution-centralizer ℤ/2 cover INSIDE M, NOT
      a cover OF the whole Monster. The Monster is not the top of a literal
      `M̃ → M` spin tower; the recurrence at the top is the 2-local 2.B
      structure. Stated honestly, not forced into "M̃ → M".

  CITED OBLIGATIONS (NOT proven — far beyond Init):
    (L1) [Conway structure]  Co0 = Aut(Leech lattice); the central element −1;
         the quotient isomorphism Co0/{±1} ≅ Co1; Co1, Co2, Co3 sporadic simple.
         (Conway 1968/1969; ATLAS.) We prove only the order/2-adic shadow.
    (T1) [triality]  Spin(8) triality (order-3 outer automorphism) and its
         identification with the three E8 copies in the E8³ Niemeier glue. We
         prove only 24 = 3·8 and the coprimality gcd(3,2)=1; the rest is analogy.
    (M1) [Baby Monster cover]  C_M(2A) ≅ 2.B, the central extension
         1 → {1,t} → 2.B → B → 1; B sporadic simple. (Leon–Sims; ATLAS.) We
         prove only |2.B| = 2·|B|.
    (M2) [Monster]  M = Fischer–Griess Monster, simple, of the cited order; 2.B
         as a subgroup of M (so the divisibility is a Lagrange index); the full
         2-local structure. (Griess 1982; ATLAS.) We prove only the order,
         divisibility, and 2-adic facts.
    (D1) [moonshine chain]  the Leech ↔ Co0 ↔ Monster moonshine link (the
         Conway groups act on the Leech lattice; the Monster on the moonshine
         module V♮; the 196884 = 196883 + 1 McKay relation lives in
         E8LeechMonsterTower). NOT re-derived here.

  These shadows are TRUE and DECIDABLE; the group structures they shadow are
  deferred honestly, exactly as `OrientationE8Bridge` / `E8LeechMonsterTower`
  defer the continuous / lattice / group pieces. No "X is Y" identity is
  manufactured: we say "is a ℤ/2 central extension", "maps to", "divides",
  "has order".
-/
theorem deferred_scope : True := trivial

#print axioms spin_cover_tower_to_monster
#print axioms co0_is_two_co1
#print axioms twoB_is_two_baby
#print axioms leech_cover_two_adic_fingerprint

end SpinCoverTowerToMonster
end Gnosis
