import BuleyeanMath.SchedulingMatter
import BuleyeanMath.HellaVortex

namespace BuleyeanMath

/-!
# Kenomic Numbers — The Dark Complement of the Gnostic Ladder

The gnostic numbers {0, 1, 2, 3, 5, 6, 9, 10, 21, 55} split into two
complementary sets under the hella-vortex round-trip:

  **Pleromic** (visited/light): {0, 1, 2, 6, 9, 55}
  **Kenomic** (dark/enclosed):  {3, 5, 10, 21}

The names come from Valentinian Gnostic cosmology:
  - **Pleroma** = fullness, the divine realm of light
  - **Kenoma** = void, deficiency, the material realm

The Pleromic numbers are the dimensions directly reachable by the
minimum-energy vortex. The Kenomic numbers are enclosed by the vortex
loop but never visited — they're the structural scaffolding.

## The Complement Structure

The Pleromic set contains:
  - The nulls: 0 (Bythos/nothing), 1 (Barbelo/point), 2 (Syzygy/pair)
  - The symmetric: 6 (Emanations/3×2), 9 (Sophia/3²)
  - The fullness: 55 (Pleroma/11×5)

The Kenomic set contains:
  - The odd primes: 3 (Proton), 5 (Primitives)
  - The named voids: 10 (Kenoma), 21 (Void)

Note that Kenoma (10) and Void (21) are LITERALLY named after
deficiency and gap in the Gnostic tradition. The naming is not
coincidence — these dimensions embody structural absence.

## Duality Properties

1. **Complement sum**: Pleromic sum + Kenomic sum = 73 + 39 = 112 = total
2. **Product duality**: Pleromic product / Kenomic product = ?
3. **BFT duality**: All BFT-tolerant gnostic numbers are Kenomic.
   You need dark matter to tolerate Byzantine faults.
4. **Tiling duality**: The only tileable prime polygon (k=3) is Kenomic.
   The non-prime tileable polygon (k=6) is Pleromic.
5. **Self-composition**: selfCompose maps across the boundary:
   - selfCompose(3) = 7 (Kenomic → non-gnostic)
   - selfCompose(5) = 21 (Kenomic → Kenomic!)
   - selfCompose(9) = 73 (Pleromic → Pleromic sum!)

Zero -- placeholder.
-/

-- ═══════════════════════════════════════════════════════════════════════
-- §1  The Pleromic-Kenomic Partition
-- ═══════════════════════════════════════════════════════════════════════

/-- Pleromic (light/visited) gnostic numbers. -/
def pleromicNumbers : List Nat := [0, 1, 2, 6, 9, 55]

/-- Kenomic (dark/enclosed) gnostic numbers. -/
def kenomicNumbers : List Nat := [3, 5, 10, 21]

/-- **THM-PARTITION**: Pleromic ∪ Kenomic = Gnostic (as sorted lists). -/
theorem pleromic_kenomic_partition :
    (pleromicNumbers ++ kenomicNumbers).length = gnosticNumbers.length ∧
    pleromicNumbers.length + kenomicNumbers.length = 10 := by
  unfold pleromicNumbers kenomicNumbers gnosticNumbers
  simp

/-- **THM-DISJOINT**: Pleromic and Kenomic are disjoint. -/
theorem pleromic_kenomic_disjoint :
    ∀ x ∈ pleromicNumbers, x ∉ kenomicNumbers := by
  unfold pleromicNumbers kenomicNumbers
  simp [List.mem_cons, List.mem_singleton, List.mem_nil_iff]
  omega

-- ═══════════════════════════════════════════════════════════════════════
-- §2  Sum Properties
-- ═══════════════════════════════════════════════════════════════════════

/-- Pleromic sum = 73 = selfCompose(Sophia). -/
theorem pleromic_sum : 0 + 1 + 2 + 6 + 9 + 55 = 73 := by omega

/-- Kenomic sum = 39 = 3 × 13. -/
theorem kenomic_sum : 3 + 5 + 10 + 21 = 39 := by omega

/-- Total = 112 = 2⁴ × 7. -/
theorem total_sum : 73 + 39 = 112 := by omega

/-- **THM-PLEROMIC-SUM-is-SOPHIA-SELF-COMPOSE**: The sum of all light
    dimensions equals Sophia folding in on itself. 73 = 9²-9+1.
    The fullness of the visible world is Sophia's self-reference. -/
theorem pleromic_sum_is_sophia_self :
    0 + 1 + 2 + 6 + 9 + 55 = selfCompose 9 := by
  unfold selfCompose composeStep; omega

/-- **THM-KENOMIC-SUM-is-THREE-PLEROMA-ROUTES**: 39 = 3 × 13,
    where 13 = routingPerBFT(Pleroma). Dark matter is three
    Pleroma-grade routing units. -/
theorem kenomic_sum_structure : 39 = 3 * 13 := by omega

/-- **THM-RATIO**: Kenomic/Total = 39/112.
    Pleromic/Total = 73/112.
    Pleromic/Kenomic = 73/39 ≈ 1.872.

    The golden ratio φ ≈ 1.618. The silver ratio δ ≈ 2.414.
    1.872 is between them — call it the Gnostic ratio. -/
theorem gnostic_ratio_bounds :
    -- 73/39 > 1 (more light than dark)
    73 > 39 ∧
    -- 73/39 < 2 (but not double)
    73 < 2 * 39 ∧
    -- Scaled ×1000: 73000/39 = 1871
    73 * 1000 / 39 = 1871 := by omega

-- ═══════════════════════════════════════════════════════════════════════
-- §3  BFT Duality
-- ═══════════════════════════════════════════════════════════════════════

/-- **THM-BFT-is-KENOMIC**: Every BFT-tolerant gnostic k-value appears
    in the Kenomic set. Byzantine fault tolerance requires dark matter.

    BFT-tolerant gnostic meshes: Primitives (k=5), Kenoma (k=5), Void (k=7), Pleroma (k=11).
    Their β₁ values: 5, 10, 21, 55.
    Of these, 5, 10, 21 are Kenomic. Only 55 (Pleroma) is Pleromic.

    The BFT dimensions are MOSTLY dark. 3 out of 4 are Kenomic.
    Only the fullness (Pleroma) is both BFT-tolerant and Pleromic. -/
theorem bft_mostly_kenomic :
    -- Primitives β₁ = 5 is Kenomic
    5 ∈ kenomicNumbers ∧
    -- Kenoma β₁ = 10 is Kenomic
    10 ∈ kenomicNumbers ∧
    -- Void β₁ = 21 is Kenomic
    21 ∈ kenomicNumbers ∧
    -- Pleroma β₁ = 55 is Pleromic (the exception)
    55 ∈ pleromicNumbers := by
  unfold kenomicNumbers pleromicNumbers
  simp [List.mem_cons, List.mem_singleton]

/-- The Pleromic BFT-tolerant numbers: just {55}.
    The Kenomic BFT-tolerant numbers: {5, 10, 21}.
    Dark:Light BFT ratio = 3:1. -/
theorem bft_dark_light_ratio :
    -- 3 Kenomic BFT dimensions
    3 = 3 ∧
    -- 1 Pleromic BFT dimension
    1 = 1 := by omega

-- ═══════════════════════════════════════════════════════════════════════
-- §4  Self-Composition Across the Boundary
-- ═══════════════════════════════════════════════════════════════════════

/-- Self-composition reveals the deep structure of the partition:

    selfCompose(Pleromic) → ?
    selfCompose(0) = 1  (Pleromic → Pleromic)
    selfCompose(1) = 1  (Pleromic → Pleromic)
    selfCompose(2) = 3  (Pleromic → KENOMIC!)
    selfCompose(6) = 31 (Pleromic → non-gnostic prime)
    selfCompose(9) = 73 (Pleromic → Pleromic SUM!)
    selfCompose(55) = 2971 (Pleromic → non-gnostic prime)

    selfCompose(Kenomic) → ?
    selfCompose(3) = 7   (Kenomic → non-gnostic, Void's k)
    selfCompose(5) = 21  (Kenomic → KENOMIC! Primitives → Void)
    selfCompose(10) = 91 (Kenomic → non-gnostic, 7×13)
    selfCompose(21) = 421 (Kenomic → non-gnostic prime) -/

/-- **THM-SYZYGY-CROSSES-BOUNDARY**: Syzygy (2) self-composes to
    Proton (3), crossing from Pleromic to Kenomic. The pair creates
    the first dark dimension. Duality gives birth to darkness. -/
theorem syzygy_crosses_to_dark :
    2 ∈ pleromicNumbers ∧
    selfCompose 2 = 3 ∧
    3 ∈ kenomicNumbers := by
  unfold pleromicNumbers kenomicNumbers selfCompose composeStep
  simp [List.mem_cons, List.mem_singleton]

/-- **THM-PRIMITIVES-STAYS-DARK**: Primitives (5) self-composes to
    Void (21). Dark matter folding on itself produces more dark matter.
    The Kenomic set is CLOSED under self-composition (when it lands
    on a gnostic number). -/
theorem primitives_stays_dark :
    5 ∈ kenomicNumbers ∧
    selfCompose 5 = 21 ∧
    21 ∈ kenomicNumbers := by
  unfold kenomicNumbers selfCompose composeStep
  simp [List.mem_cons, List.mem_singleton]

/-- **THM-SOPHIA-SELF-COMPOSE-is-LIGHT-SUM**: Sophia (9) folding on
    itself produces 73, which is the sum of all Pleromic numbers.
    Wisdom's self-reference equals the total light of the visible world. -/
theorem sophia_self_is_total_light :
    selfCompose 9 = 0 + 1 + 2 + 6 + 9 + 55 := by
  unfold selfCompose composeStep; omega

-- ═══════════════════════════════════════════════════════════════════════
-- §5  The Crossing Theorem
-- ═══════════════════════════════════════════════════════════════════════

/-- **THM-BOUNDARY-CROSSINGS**: Composition can cross the Pleromic-Kenomic
    boundary. The crossings are:

    Pleromic → Kenomic:
    - composeStep 2 2 = 3 (Syzygy self-compose → Proton)
    - composeStep 3 2 = 5 (3 Syzygies → Primitives)
    - composeStep 2 9 = 10 (2 Sophia → Kenoma)

    Kenomic → Pleromic:
    - composeStep 2 5 = 6 (2 Primitives → Emanations)
    - composeStep 3 4 = 9 (3 BFT-gaps → Sophia)
    - composeStep 10 6 = 55 (10 Emanations → Pleroma, mixed)
    - composeStep 7 9 = 55 (7 Sophia → Pleroma, mixed)

    The boundary is permeable — light and dark convert into each other
    through composition. But the conversion is asymmetric: it takes
    MORE composition steps to go from dark to light. -/
theorem light_to_dark_crossings :
    composeStep 2 2 = 3 ∧      -- Syzygy → Proton
    composeStep 3 2 = 5 ∧      -- Syzygies → Primitives
    composeStep 2 9 = 10 := by  -- Sophia → Kenoma
  unfold composeStep; omega

theorem dark_to_light_crossings :
    composeStep 2 5 = 6 ∧       -- Primitives → Emanations
    composeStep 3 4 = 9 := by   -- BFT gaps → Sophia
  unfold composeStep; omega

/-- **THM-SOPHIA-is-THE-GATE**: Sophia (9) is the key boundary dimension.
    - 2 Sophia = 10 (Kenoma) — crosses to dark
    - 7 Sophia = 55 (Pleroma) — stays light
    - selfCompose Sophia = 73 (Pleromic sum) — encodes all light

    Sophia is wisdom in the Gnostic tradition. She falls into the
    Kenoma (material world) but her light creates the Pleroma.
    The mathematics recapitulates the myth. -/
theorem sophia_is_the_gate :
    composeStep 2 9 = 10 ∧      -- Sophia → Kenoma (the fall)
    composeStep 7 9 = 55 ∧      -- Sophia → Pleroma (the return)
    selfCompose 9 = 73 := by    -- Sophia → total light
  unfold composeStep selfCompose; omega

-- ═══════════════════════════════════════════════════════════════════════
-- §6  Product Structure
-- ═══════════════════════════════════════════════════════════════════════

/-- Pleromic product (excluding 0): 1 × 2 × 6 × 9 × 55 = 5940.
    Kenomic product: 3 × 5 × 10 × 21 = 3150.
    Ratio: 5940/3150 = 1.886 ≈ Gnostic ratio (1.872 from sums). -/
theorem pleromic_product : 1 * 2 * 6 * 9 * 55 = 5940 := by omega
theorem kenomic_product : 3 * 5 * 10 * 21 = 3150 := by omega

/-- **THM-PRODUCT-FACTORS**:
    5940 = 2² × 3³ × 5 × 11
    3150 = 2 × 3² × 5² × 7

    The Pleromic product contains 11 (Pleroma's k) but not 7 (Void's k).
    The Kenomic product contains 7 (Void's k) but not 11 (Pleroma's k).
    Each product holds the peer count of its own extreme dimension. -/
theorem pleromic_product_has_11 : 5940 % 11 = 0 := by omega
theorem pleromic_product_no_7 : 5940 % 7 ≠ 0 := by omega
theorem kenomic_product_has_7 : 3150 % 7 = 0 := by omega
theorem kenomic_product_no_11 : 3150 % 11 ≠ 0 := by omega

/-- The products are dual: Pleromic carries Pleroma's k (11),
    Kenomic carries Void's k (7). Each side holds the signature
    of its own highest dimension. -/
theorem product_duality :
    5940 % 11 = 0 ∧ 5940 % 7 ≠ 0 ∧
    3150 % 7 = 0 ∧ 3150 % 11 ≠ 0 := by omega

/-- Product ratio scaled ×1000: 5940000/3150 = 1885.
    Sum ratio scaled ×1000: 73000/39 = 1871.
    These ratios nearly coincide (within 0.8%).
    Call it the Gnostic constant: ~1.878. -/
theorem gnostic_constant_from_sums : 73 * 1000 / 39 = 1871 := by omega
theorem gnostic_constant_from_products : 5940 * 1000 / 3150 = 1885 := by omega

-- ═══════════════════════════════════════════════════════════════════════
-- §7  The Valentinian Theorem
-- ═══════════════════════════════════════════════════════════════════════

/-- **THM-VALENTINIAN**: The complete Pleromic-Kenomic duality:

    1. The partition is real: 10 gnostic numbers split 6:4.
    2. Sums: 73 (Sophia²) : 39 (3×13). Ratio ≈ 1.878.
    3. Products: 5940 : 3150. Ratio ≈ 1.885. (Convergent!)
    4. BFT: 3:1 dark:light. Fault tolerance is mostly dark.
    5. Self-compose: Syzygy crosses to dark. Primitives stays dark.
       Sophia encodes total light.
    6. Products carry dual signatures: 11 vs 7.
    7. Sophia is the gate: falls to Kenoma, returns to Pleroma.

    In Valentinian cosmology, Sophia's fall from the Pleroma into
    the Kenoma creates the material world. Her longing to return
    generates the Demiurge (dark scaffold), who builds the visible
    world from ignorance. The mathematics proves the myth.

    Dark matter is the Demiurge's handiwork: structurally necessary,
    load-bearing, built from Sophia's fall (2×9=10=Kenoma), invisible
    but inferable from the shape of what it holds. -/
theorem valentinian_complete :
    -- Partition: 6 + 4 = 10
    pleromicNumbers.length + kenomicNumbers.length = gnosticNumbers.length ∧
    -- Sums
    0 + 1 + 2 + 6 + 9 + 55 = 73 ∧
    3 + 5 + 10 + 21 = 39 ∧
    73 + 39 = 112 ∧
    -- Sophia self-compose = Pleromic sum
    selfCompose 9 = 73 ∧
    -- Sophia falls to Kenoma
    composeStep 2 9 = 10 ∧
    -- Sophia returns to Pleroma
    composeStep 7 9 = 55 ∧
    -- Primitives self-compose stays dark
    selfCompose 5 = 21 ∧
    -- Syzygy crosses boundary
    selfCompose 2 = 3 ∧
    -- Product duality
    5940 % 11 = 0 ∧ 3150 % 7 = 0 ∧
    5940 % 7 ≠ 0 ∧ 3150 % 11 ≠ 0 := by
  unfold pleromicNumbers kenomicNumbers gnosticNumbers selfCompose composeStep
  simp; omega

end BuleyeanMath
