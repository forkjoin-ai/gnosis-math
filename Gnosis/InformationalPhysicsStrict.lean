/-
  InformationalPhysicsStrict.lean
  ===============================

  Closes gap #1 from the InformationalPhysics honest-verdict-review
  (2026-05-10): the original crown theorem `informationalPhysicsMaster`
  proved `informational ≤ naive`, which is true but weak — the
  inequality holds even for an empty stack or a degenerate "identity"
  layer that gives no savings.

  This file builds the *strict* crown that fires whenever the layer
  stack contains at least one strictly-improving layer (`bytes_per_unit
  < 16`). Under that hypothesis (and `units > 0`), the
  informational-physics byte count is strictly less than the naive
  baseline.

  ══════════════════════════════════════════════════════════════════════
  ## Why this matters
  ══════════════════════════════════════════════════════════════════════

  The original crown (`≤`) is satisfiable trivially: feed it an empty
  stack and the inequality `units * 16 ≤ units * 16` discharges by
  reflexivity, but no wire savings are realised. The narrative claim
  of the InformationalPhysics frame ("each layer hands the byte budget
  back") is a *strict* statement: any non-trivial layer wins bytes.

  The strict crown formalises that narrative claim:

      hasStrictlyImprovingLayer layers  ∧  units > 0
        →  informationalByteCount layers units  <  naiveByteCount units

  All six canonical wire-diet layers (layer0 .. layer5) are strictly
  improving — every per-unit proxy beats 16. So any non-empty subset
  of the canonical six fires the strict crown immediately.

  ══════════════════════════════════════════════════════════════════════
  ## Style
  ══════════════════════════════════════════════════════════════════════

  Init-only, zero `omega`, zero `simp` on open goals, zero `sorry`,
  zero new `axiom`. Closed numeric witnesses use `decide`. Strict
  multiplication step uses `Nat.mul_lt_mul_left` with the supplied
  `units > 0` hypothesis.

  ══════════════════════════════════════════════════════════════════════
  ## What this file pins
  ══════════════════════════════════════════════════════════════════════

  1. `isStrictlyImproving`           — predicate `bytes_per_unit < 16`.
  2. `hasStrictlyImprovingLayer`     — `∃ l ∈ layers, isStrictlyImproving l`.
  3. `min_bytes_le_each`             — helper: min ≤ each element.
  4. `min_bytes_lt_naive_of_strict`  — strict member ⇒ min < 16.
  5. `informationalPhysicsStrictMaster` — THE STRICT CROWN.
  6. `layerN_is_strictly_improving`  — six concrete witnesses (N=0..5).
  7. `canonical_strict_master`       — any non-empty canonical subset
                                        fires the strict crown.
  8. `strict_savings_grow_with_units`— gap is monotone in `units`.
  9. `workload1_strictly_below_base64` — pinned 95 < 155.
 10. `workload2_strictly_below_base64` — pinned 350 < 1400.
-/

import Init
import Gnosis.InformationalPhysics

namespace InformationalPhysics

/-! ══════════════════════════════════════════════════════════════════
    ## §1. Strict-improvement predicate
    ══════════════════════════════════════════════════════════════════

    A layer is *strictly* improving if its per-unit byte cost beats
    the naive base64 baseline (16 bytes/unit). This is the hypothesis
    that strengthens `≤` to `<` in the crown. -/

/-- A `LayerOptimal` is strictly improving when its per-unit cost
    is below the naive 16-byte baseline. This is the cleanest
    structural form of "the layer wins bytes on every unit". -/
def isStrictlyImproving (l : LayerOptimal) : Prop :=
  l.bytes_per_unit < 16

/-- The strict-improvement predicate is decidable on `Nat`. -/
instance (l : LayerOptimal) : Decidable (isStrictlyImproving l) :=
  inferInstanceAs (Decidable (l.bytes_per_unit < 16))

/-- A layer stack contains at least one strictly-improving layer. -/
def hasStrictlyImprovingLayer (layers : List LayerOptimal) : Prop :=
  ∃ l, l ∈ layers ∧ isStrictlyImproving l

/-! ══════════════════════════════════════════════════════════════════
    ## §2. Helper — min ≤ each element
    ══════════════════════════════════════════════════════════════════

    `minBytesPerUnit` is the conservative cheapest-applicable-layer
    bound. For any element of the list, the min is at most that
    element's per-unit cost. Proved by structural induction. -/

/-- The min per-unit cost across a list is at most each member's
    per-unit cost. Structural induction on the list; in the cons
    case the `if` branches both bound the min by `l.bytes_per_unit`
    or by `restMin ≤ rhs.bytes_per_unit` (using the inductive
    hypothesis). -/
theorem min_bytes_le_each (layers : List LayerOptimal) (l : LayerOptimal)
    (h : l ∈ layers) :
    minBytesPerUnit layers ≤ l.bytes_per_unit := by
  induction layers with
  | nil =>
      -- `l ∈ []` is impossible; eliminate the membership proof directly.
      cases h
  | cons head tail ih =>
      -- Either `l = head` or `l ∈ tail`.
      rcases List.mem_cons.mp h with h_eq | h_tail
      · -- l = head: min ≤ head.bytes_per_unit by definition of min.
        subst h_eq
        unfold minBytesPerUnit
        by_cases hcase : l.bytes_per_unit < minBytesPerUnit tail
        · rw [if_pos hcase]
          exact Nat.le_refl _
        · rw [if_neg hcase]
          exact Nat.le_of_not_lt hcase
      · -- l ∈ tail: ih gives min(tail) ≤ l.bytes_per_unit; chain
        -- through min(head :: tail) ≤ min(tail).
        unfold minBytesPerUnit
        by_cases hcase : head.bytes_per_unit < minBytesPerUnit tail
        · rw [if_pos hcase]
          -- head.bytes_per_unit < minBytesPerUnit tail ≤ l.bytes_per_unit.
          exact Nat.le_trans (Nat.le_of_lt hcase) (ih h_tail)
        · rw [if_neg hcase]
          exact ih h_tail

/-! ══════════════════════════════════════════════════════════════════
    ## §3. Strict member ⇒ min < 16
    ══════════════════════════════════════════════════════════════════ -/

/-- If a layer stack contains at least one strictly-improving layer,
    then the min per-unit cost is strictly less than 16. -/
theorem min_bytes_lt_naive_of_strict (layers : List LayerOptimal)
    (h_strict : hasStrictlyImprovingLayer layers) :
    minBytesPerUnit layers < 16 := by
  rcases h_strict with ⟨l, h_mem, h_lt⟩
  -- min ≤ l.bytes_per_unit (helper) and l.bytes_per_unit < 16.
  exact Nat.lt_of_le_of_lt (min_bytes_le_each layers l h_mem) h_lt

/-! ══════════════════════════════════════════════════════════════════
    ## §4. THE STRICT CROWN — `informationalPhysicsStrictMaster`
    ══════════════════════════════════════════════════════════════════

    Whenever the layer stack contains a strictly-improving member
    AND the workload is non-empty (`units > 0`), the
    informational-physics byte count is strictly less than the naive
    baseline. The positivity hypothesis is essential: with `units = 0`
    both sides are 0 and the strict inequality fails. -/

/-- THE STRICT CROWN. For any workload of `units > 0` units and any
    layer stack containing at least one strictly-improving layer
    (`bytes_per_unit < 16`), the informational-physics byte count is
    strictly below the naive baseline. -/
theorem informationalPhysicsStrictMaster
    (layers : List LayerOptimal) (units : Nat)
    (h_strict : hasStrictlyImprovingLayer layers)
    (h_units : units > 0) :
    informationalByteCount layers units < naiveByteCount units := by
  unfold informationalByteCount naiveByteCount
  -- Goal: `units * minBytesPerUnit layers < units * 16`.
  exact (Nat.mul_lt_mul_left h_units).mpr
          (min_bytes_lt_naive_of_strict layers h_strict)

/-! ══════════════════════════════════════════════════════════════════
    ## §5. Concrete witnesses — all six canonical layers strict
    ══════════════════════════════════════════════════════════════════

    Every canonical wire-diet layer (layer0..layer5) has
    `bytes_per_unit ∈ {0, 1, 3, 7}`, all of which are < 16. So all
    six fire the strict crown when included in a non-empty stack on a
    non-empty workload. -/

/-- Layer 0 (`PerByteAlphabet`, bwDense): 7 < 16. -/
theorem layer0_is_strictly_improving : isStrictlyImproving layer0Optimal := by
  decide

/-- Layer 1 (`FrameStructure`): 0 < 16. -/
theorem layer1_is_strictly_improving : isStrictlyImproving layer1Optimal := by
  decide

/-- Layer 2 (`IntegerCoding`, Zeckendorf): 1 < 16. -/
theorem layer2_is_strictly_improving : isStrictlyImproving layer2Optimal := by
  decide

/-- Layer 3 (`OrderingFree`, Lehmer/factoradic): 0 < 16. -/
theorem layer3_is_strictly_improving : isStrictlyImproving layer3Optimal := by
  decide

/-- Layer 4 (`StatisticalPrior`, POSDICT): 1 < 16. -/
theorem layer4_is_strictly_improving : isStrictlyImproving layer4Optimal := by
  decide

/-- Layer 5 (`AlphabetSubstrate`, phoneme codec): 3 < 16. -/
theorem layer5_is_strictly_improving : isStrictlyImproving layer5Optimal := by
  decide

/-- All six canonical wire-diet layers are strictly improving. The
    framework has *no* trivial / identity layer — every row of
    WIRE_DIET.md hands real byte budget back. -/
theorem all_six_canonical_layers_strict :
    isStrictlyImproving layer0Optimal ∧
    isStrictlyImproving layer1Optimal ∧
    isStrictlyImproving layer2Optimal ∧
    isStrictlyImproving layer3Optimal ∧
    isStrictlyImproving layer4Optimal ∧
    isStrictlyImproving layer5Optimal :=
  ⟨layer0_is_strictly_improving,
   layer1_is_strictly_improving,
   layer2_is_strictly_improving,
   layer3_is_strictly_improving,
   layer4_is_strictly_improving,
   layer5_is_strictly_improving⟩

/-! ══════════════════════════════════════════════════════════════════
    ## §6. Canonical strict crown — non-empty canonical subset wins
    ══════════════════════════════════════════════════════════════════

    Any non-empty stack whose head is one of the six canonical
    layers fires the strict crown on any positive workload. This is
    the cleanest packaged consequence: pick any canonical layer,
    stack whatever you like behind it, and on any non-empty
    workload you strictly beat base64. -/

/-- For any non-empty layer stack whose head is one of the six
    canonical wire-diet layers, the strict crown inequality holds on
    any positive workload. -/
theorem canonical_strict_master
    (l : LayerOptimal) (rest : List LayerOptimal) (units : Nat)
    (hl : l = layer0Optimal ∨ l = layer1Optimal ∨ l = layer2Optimal
        ∨ l = layer3Optimal ∨ l = layer4Optimal ∨ l = layer5Optimal)
    (h_units : units > 0) :
    informationalByteCount (l :: rest) units < naiveByteCount units := by
  apply informationalPhysicsStrictMaster (l :: rest) units _ h_units
  -- Build `hasStrictlyImprovingLayer (l :: rest)` from the canonical
  -- case analysis on `l`.
  refine ⟨l, List.mem_cons_self, ?_⟩
  rcases hl with h | h | h | h | h | h <;>
    (subst h; decide)

/-! ══════════════════════════════════════════════════════════════════
    ## §7. Scaling — the byte-count gap grows with workload size
    ══════════════════════════════════════════════════════════════════

    When the strict hypothesis holds, the gap `naive - informational`
    is monotone non-decreasing in `units`: doubling the workload at
    least doubles the byte savings. This pins the operator-facing
    intuition that the diet pays off more on big payloads. -/

/-- The byte-count gap (`naive - informational`) is monotone
    non-decreasing in the workload size. Stated structurally as:
    increasing `units` from `u₁` to `u₂` (with `u₁ ≤ u₂`) does not
    shrink the gap.

    Concretely: `gap(u) = u * (16 - minBytes)`. Multiplying by
    larger `u` yields at-least-as-large gap. The strict hypothesis
    `h_strict` is recorded for narrative clarity (the gap is
    strictly *positive* under it) but the monotonicity proof holds
    regardless. -/
theorem strict_savings_grow_with_units
    (layers : List LayerOptimal)
    (_h_strict : hasStrictlyImprovingLayer layers)
    (u₁ u₂ : Nat) (h_le : u₁ ≤ u₂) :
    (naiveByteCount u₁ - informationalByteCount layers u₁)
      ≤ (naiveByteCount u₂ - informationalByteCount layers u₂) := by
  unfold naiveByteCount informationalByteCount
  -- Both gap = u * (16 - minBytes); use distributivity + monotone mul.
  -- u * 16 - u * minBytes = u * (16 - minBytes) via Nat.mul_sub_left_distrib.
  rw [← Nat.mul_sub_left_distrib u₁ 16 (minBytesPerUnit layers),
      ← Nat.mul_sub_left_distrib u₂ 16 (minBytesPerUnit layers)]
  exact Nat.mul_le_mul_right (16 - minBytesPerUnit layers) h_le

/-! ══════════════════════════════════════════════════════════════════
    ## §8. Workload witnesses — pinned strict savings
    ══════════════════════════════════════════════════════════════════

    The two WIRE_DIET.md "Cumulative diet" witnesses re-stated as
    instances of the strict crown. -/

/-- Workload 1 (2-frame ~100 B tunnel response): 95 < 155 bytes.
    The strict savings come from layer 0 (bwDense) + layer 1 (frame
    elimination) + layer 3 (ordering free). -/
theorem workload1_strictly_below_base64 :
    workload1_bwdense_l1_l3 < workload1_base64_chars := by decide

/-- Workload 2 (1 MB FASTA): 350 KB < 1400 KB. Layer 0 + Layer 4
    (DNA prior) → 4× reduction. -/
theorem workload2_strictly_below_base64 :
    workload2_bwdense_l4dna_kb < workload2_base64_kb := by decide

/-! ══════════════════════════════════════════════════════════════════
    ## §9. Bundled strict crown
    ══════════════════════════════════════════════════════════════════

    Single packaged theorem combining the strict crown with the
    structural witnesses. Useful for downstream modules that depend
    on the strict claim as a single hypothesis. -/

/-- The strict crown package:
      (a) all six canonical layers are strictly improving;
      (b) any canonical-headed stack on any positive workload
          strictly beats base64;
      (c) workload-1 pinned 95 < 155;
      (d) workload-2 pinned 350 < 1400. -/
theorem informationalPhysicsStrictCrown :
    (isStrictlyImproving layer0Optimal ∧
       isStrictlyImproving layer1Optimal ∧
       isStrictlyImproving layer2Optimal ∧
       isStrictlyImproving layer3Optimal ∧
       isStrictlyImproving layer4Optimal ∧
       isStrictlyImproving layer5Optimal) ∧
    (∀ units : Nat, units > 0 →
        informationalByteCount [layer0Optimal] units
          < naiveByteCount units) ∧
    (workload1_bwdense_l1_l3 < workload1_base64_chars) ∧
    (workload2_bwdense_l4dna_kb < workload2_base64_kb) :=
  ⟨all_six_canonical_layers_strict,
   (fun units h_units =>
     canonical_strict_master layer0Optimal [] units (Or.inl rfl) h_units),
   workload1_strictly_below_base64,
   workload2_strictly_below_base64⟩

end InformationalPhysics
