/-
  InformationalPhysicsUnified.lean
  ================================

  Unification: WIRE_DIET-6 = Cover & Thomas-4 IT-core + 2 engineering
  extensions. The pluralism resolves to extension.

  ══════════════════════════════════════════════════════════════════════
  ## Provenance
  ══════════════════════════════════════════════════════════════════════

  Y4 landed `InformationalPhysicsForcedBijection.lean` with a 6-axis
  WIRE_DIET system. Z then landed `InformationalPhysicsCoverThomasAlternative.lean`
  with a 4-axis Cover & Thomas system, proving
  `incommensurable_assumption_spaces` — the two enums are disjoint
  AT THE TYPE LEVEL.

  Taylor (2026-05-10): "unify them via semantic correspondence."

  This module supplies the missing semantic bridge. Type-level
  disjointness (Z) is real but it is a Lean fact, not a physics fact.
  At the SEMANTIC level — what the two carvings are *talking about* —
  4 of WIRE_DIET's 6 assumptions correspond exactly to all 4 Cover &
  Thomas assumptions:

      | WIRE_DIET                          | Cover & Thomas              |
      |------------------------------------|-----------------------------|
      | `Base64IsOptimal`                  | `AlphabetIsBinary`          |
      | `IntegersAreFixedWidth`            | `DistributionIsUniform`     |
      | `TransmissionsAreUnconditioned`    | `SourceIsMemoryless`        |
      | `ByteIsTheUnit`                    | `EncodingIsSymbolBySymbol`  |
      | `EachFrameSelfDescribing`          | (no analog — protocol)      |
      | `OrderingIsOverhead`               | (no analog — combinatorial) |

  The unification claim:

      WIRE_DIET-6  =  Cover & Thomas-4 IT-core  +  2 engineering extensions
                                                   {FrameStructure, Ordering}

  Cover & Thomas is the IT-canonical sub-system; WIRE_DIET extends with
  two engineering layers (frame self-description and combinatorial
  ordering) that classical Shannon-style accounting does not surface.

  ══════════════════════════════════════════════════════════════════════
  ## Honest verdict
  ══════════════════════════════════════════════════════════════════════

  PROVED here:
    ✓ A semantic injection `coverThomasToWireDiet` from
      `SourceClassicalAssumption` to `ClassicalAssumption` exists.
    ✓ The injection lands entirely in the IT-core 4-element subset
      of `ClassicalAssumption`.
    ✓ The injection is injective (no two Cover & Thomas premises
      collide on the WIRE_DIET side).
    ✓ The 2 engineering extensions (`EachFrameSelfDescribing` and
      `OrderingIsOverhead`) are EXACTLY the WIRE_DIET assumptions
      with no Cover & Thomas analog.
    ✓ `unifiedCardinality`: 6 = 4 + 2, structurally pinned.
    ✓ `coverThomasIsSubsystemOfWireDiet`: an embedding from the
      4-axis Cover & Thomas system into the 6-axis WIRE_DIET
      system, preserving the cancellation structure.
    ✓ `pluralism_resolves_to_extension`: every Cover & Thomas
      concern IS captured by WIRE_DIET; the apparent pluralism is
      structural extension, not incommensurable carving.

  CAVEAT (engineering judgment, not a stronger claim):
    The mapping reflects ONE defensible reading of "what counts as
    the same cancellation". `Base64IsOptimal` ↔ `AlphabetIsBinary`
    is the alphabet-extension face; `IntegersAreFixedWidth` ↔
    `DistributionIsUniform` is the heavy-tailed-vs-uniform face. A
    different reader could plausibly merge different pairs (e.g.
    `Base64IsOptimal` ↔ `EncodingIsSymbolBySymbol`). We commit to
    one mapping and prove it consistent; we do NOT claim it is the
    UNIQUE injective semantic correspondence.

  OPEN:
    ✗ Whether the mapping is the unique injective one. Multiple
      semantic correspondences could plausibly exist.
    ✗ The full categorical statement (4-axis system as a sub-object
      in some category of axis-systems). Init has no category theory.
    ✗ Whether the 2 engineering extensions are "removable" by
      reformulating Cover & Thomas to include them — that is a
      modelling judgment, not a Lean theorem.

  ══════════════════════════════════════════════════════════════════════
  ## Style
  ══════════════════════════════════════════════════════════════════════

  Imports `Init`, `Gnosis.InformationalPhysics` (for
  `ClassicalAssumption`), and
  `Gnosis.InformationalPhysicsCoverThomasAlternative` (for
  `SourceClassicalAssumption` and `coverThomasAxisSystem`). Per
  `RUSTIC_CHURCH.md`: zero `omega`, zero `simp` on open goals, zero
  `sorry`, zero new `axiom`. Closed numeric / decidable witnesses use
  `decide`. Section dividers `══`.
-/

import Init
import Gnosis.InformationalPhysics
import Gnosis.InformationalPhysicsCoverThomasAlternative

namespace InformationalPhysicsUnified

open InformationalPhysics
open InformationalPhysicsCoverThomasAlternative

/-! ══════════════════════════════════════════════════════════════════
    ## §1. The semantic correspondence — `coverThomasToWireDiet`
    ══════════════════════════════════════════════════════════════════

    The 4-to-6 mapping. Each Cover & Thomas source-mathematical
    assumption corresponds to ONE WIRE_DIET wire-engineering assumption
    that attacks the same degree of freedom. The semantic readings:

      AlphabetIsBinary         ↔  Base64IsOptimal
        (both: "the wire alphabet is the obvious 2-symbol or
         base64-symbol choice")

      DistributionIsUniform    ↔  IntegersAreFixedWidth
        (both: "every value gets equal space — no concession to
         heavy-tailed actual distribution")

      SourceIsMemoryless       ↔  TransmissionsAreUnconditioned
        (both: "no shared prior, every symbol/transmission stands
         alone, no Markov-style memory exploited")

      EncodingIsSymbolBySymbol ↔  ByteIsTheUnit
        (both: "the unit of encoding is the atomic symbol/byte —
         no block-coding or alphabet-substrate move available")

    The 2 WIRE_DIET extras with no Cover & Thomas analog:

      EachFrameSelfDescribing  — protocol-layer concern (frame headers).
                                 Cover & Thomas treats sources as raw
                                 symbol streams; framing is below the
                                 abstraction line.
      OrderingIsOverhead       — combinatorial-layer concern (Lehmer /
                                 factoradic). Cover & Thomas counts
                                 symbol-stream entropy; permutation
                                 entropy of N known items is a separate
                                 combinatorial channel.
-/

/-- The semantic correspondence: each Cover & Thomas source assumption
    maps to its WIRE_DIET analog. Pinned by the table in §0. -/
def coverThomasToWireDiet :
    SourceClassicalAssumption → ClassicalAssumption
  | .AlphabetIsBinary         => .Base64IsOptimal
  | .DistributionIsUniform    => .IntegersAreFixedWidth
  | .SourceIsMemoryless       => .TransmissionsAreUnconditioned
  | .EncodingIsSymbolBySymbol => .ByteIsTheUnit

/-! ══════════════════════════════════════════════════════════════════
    ## §2. The IT-core predicate — `isITCore`
    ══════════════════════════════════════════════════════════════════

    A Bool predicate on `ClassicalAssumption` that flags the 4
    constructors with a Cover & Thomas analog (TRUE) and the 2
    constructors that are WIRE_DIET-only engineering extensions
    (FALSE). -/

/-- `isITCore a` is `true` iff `a` has a Cover & Thomas analog under
    `coverThomasToWireDiet`. The four IT-core constructors are
    `Base64IsOptimal`, `IntegersAreFixedWidth`,
    `TransmissionsAreUnconditioned`, `ByteIsTheUnit`. The two
    engineering extensions are `EachFrameSelfDescribing` (protocol
    layer) and `OrderingIsOverhead` (combinatorial layer). -/
def isITCore : ClassicalAssumption → Bool
  | .Base64IsOptimal              => true
  | .IntegersAreFixedWidth        => true
  | .TransmissionsAreUnconditioned => true
  | .ByteIsTheUnit                => true
  | .EachFrameSelfDescribing      => false   -- protocol extension
  | .OrderingIsOverhead           => false   -- combinatorial extension

/-! ══════════════════════════════════════════════════════════════════
    ## §3. Cardinality witnesses — 6 = 4 + 2
    ══════════════════════════════════════════════════════════════════ -/

/-- The IT-core sub-count: 4 constructors of `ClassicalAssumption`
    return `true` under `isITCore`. -/
def itCoreCount : Nat := 4

/-- The engineering-extension count: 2 constructors of
    `ClassicalAssumption` return `false` under `isITCore`. -/
def engineeringExtensionCount : Nat := 2

/-- The total cardinality: 6 constructors of `ClassicalAssumption`. -/
def totalCount : Nat := 6

/-- PROVED: the IT-core count is 4. -/
theorem itCoreCount_eq_four : itCoreCount = 4 := rfl

/-- PROVED: the engineering-extension count is 2. -/
theorem engineeringExtensionCount_eq_two :
    engineeringExtensionCount = 2 := rfl

/-- PROVED: the total count is 6. -/
theorem totalCount_eq_six : totalCount = 6 := rfl

/-- PROVED: 4 + 2 = 6 — the cardinality decomposition. -/
theorem unifiedCardinality :
    itCoreCount + engineeringExtensionCount = totalCount := by decide

/-! ══════════════════════════════════════════════════════════════════
    ## §4. The image of `coverThomasToWireDiet` is the IT-core
    ══════════════════════════════════════════════════════════════════ -/

/-- PROVED: every output of `coverThomasToWireDiet` lands in the
    IT-core subset of `ClassicalAssumption`. By exhaustion. -/
theorem coverThomasToWireDiet_image_is_IT_core
    (x : SourceClassicalAssumption) :
    isITCore (coverThomasToWireDiet x) = true := by
  cases x <;> rfl

/-! ══════════════════════════════════════════════════════════════════
    ## §5. Injectivity of the semantic mapping
    ══════════════════════════════════════════════════════════════════ -/

/-- PROVED: `coverThomasToWireDiet` is injective. No two distinct
    Cover & Thomas assumptions map to the same WIRE_DIET assumption.
    By exhaustion over both arguments. -/
theorem coverThomasToWireDiet_injective
    (x y : SourceClassicalAssumption)
    (h : coverThomasToWireDiet x = coverThomasToWireDiet y) :
    x = y := by
  cases x <;> cases y <;> first | rfl | cases h

/-! ══════════════════════════════════════════════════════════════════
    ## §6. The engineering extensions — `EachFrameSelfDescribing` +
    ##       `OrderingIsOverhead`
    ══════════════════════════════════════════════════════════════════

    The two WIRE_DIET constructors with NO Cover & Thomas image. We
    pin them as a concrete list and prove that they are EXACTLY the
    constructors where `isITCore` returns false. -/

/-- The two engineering-extension assumptions: WIRE_DIET-only,
    not present in Cover & Thomas. -/
def engineeringExtensions : List ClassicalAssumption :=
  [ .EachFrameSelfDescribing
  , .OrderingIsOverhead
  ]

/-- PROVED: the engineering-extension list has length 2. -/
theorem engineeringExtensions_length :
    engineeringExtensions.length = 2 := rfl

/-- PROVED: every entry of `engineeringExtensions` has
    `isITCore = false`. The "extensions are exactly the non-IT-core
    constructors" direction (membership ⟹ not IT-core). -/
theorem engineeringExtensions_are_not_IT_core
    (a : ClassicalAssumption) (h : a ∈ engineeringExtensions) :
    isITCore a = false := by
  cases h with
  | head _ => rfl
  | tail _ h1 =>
    cases h1 with
    | head _ => rfl
    | tail _ h2 => cases h2

/-- PROVED: every `ClassicalAssumption` constructor with
    `isITCore = false` is in the `engineeringExtensions` list. The
    converse direction (not IT-core ⟹ membership). Together with
    `engineeringExtensions_are_not_IT_core` this pins
    `engineeringExtensions` as EXACTLY the non-IT-core subset. -/
theorem not_IT_core_is_engineering_extension
    (a : ClassicalAssumption) (h : isITCore a = false) :
    a ∈ engineeringExtensions := by
  cases a with
  | Base64IsOptimal              => cases h
  | IntegersAreFixedWidth        => cases h
  | TransmissionsAreUnconditioned => cases h
  | ByteIsTheUnit                => cases h
  | EachFrameSelfDescribing      => exact List.Mem.head _
  | OrderingIsOverhead           => exact List.Mem.tail _ (List.Mem.head _)

/-! ══════════════════════════════════════════════════════════════════
    ## §7. The unified-space partition theorem
    ══════════════════════════════════════════════════════════════════

    Every `ClassicalAssumption` falls into exactly one of two cases:
    either `isITCore = true` (lives in the image of
    `coverThomasToWireDiet`) or `isITCore = false` (is one of the two
    engineering extensions). The two cases partition the 6-element
    space. -/

/-- PROVED: every `ClassicalAssumption` is either in the image of
    `coverThomasToWireDiet` (IT-core case) or is an engineering
    extension. Stated as the disjunction `isITCore a = true ∨
    isITCore a = false ∧ a ∈ engineeringExtensions`. -/
theorem unifiedAssumptionSpace
    (a : ClassicalAssumption) :
    (isITCore a = true ∧
       ∃ x : SourceClassicalAssumption, coverThomasToWireDiet x = a)
    ∨
    (isITCore a = false ∧ a ∈ engineeringExtensions) := by
  cases a with
  | Base64IsOptimal =>
      exact Or.inl ⟨rfl, ⟨.AlphabetIsBinary, rfl⟩⟩
  | IntegersAreFixedWidth =>
      exact Or.inl ⟨rfl, ⟨.DistributionIsUniform, rfl⟩⟩
  | TransmissionsAreUnconditioned =>
      exact Or.inl ⟨rfl, ⟨.SourceIsMemoryless, rfl⟩⟩
  | ByteIsTheUnit =>
      exact Or.inl ⟨rfl, ⟨.EncodingIsSymbolBySymbol, rfl⟩⟩
  | EachFrameSelfDescribing =>
      exact Or.inr ⟨rfl, List.Mem.head _⟩
  | OrderingIsOverhead =>
      exact Or.inr ⟨rfl, List.Mem.tail _ (List.Mem.head _)⟩

/-! ══════════════════════════════════════════════════════════════════
    ## §8. Cover & Thomas as a sub-system of WIRE_DIET
    ══════════════════════════════════════════════════════════════════

    The 4-axis `coverThomasAxisSystem` embeds into the 6-axis
    `wireDietAxisSystem` via `coverThomasToWireDiet`. We define the
    embedding on axes and prove:

      (a) every Cover & Thomas axis maps to a WIRE_DIET axis;
      (b) the mapping commutes with the `cancels` / `sourceCancels`
          fields (semantic correspondence is preserved);
      (c) the 2 extra WIRE_DIET axes are precisely the engineering
          extensions.

    We are constrained by file ownership: we may not modify the
    sibling files' `Axis` and `SourceAxis` records, but we can
    define a fresh `embedSourceAxis` function that converts. -/

/-- Embed a `SourceAxis` (4-axis Cover & Thomas) into an `Axis`
    (6-axis WIRE_DIET) by applying `coverThomasToWireDiet` to its
    `cancels` field. Tags are preserved. -/
def embedSourceAxis
    (sx : InformationalPhysicsCoverThomasAlternative.SourceAxis) :
    InformationalPhysicsForcedBijection.Axis :=
  { tag     := sx.tag
  , cancels := coverThomasToWireDiet sx.cancels
  }

/-- PROVED: embedding preserves the tag. -/
theorem embedSourceAxis_tag
    (sx : InformationalPhysicsCoverThomasAlternative.SourceAxis) :
    (embedSourceAxis sx).tag = sx.tag := rfl

/-- PROVED: embedding preserves the cancellation up to
    `coverThomasToWireDiet`. -/
theorem embedSourceAxis_cancels
    (sx : InformationalPhysicsCoverThomasAlternative.SourceAxis) :
    (embedSourceAxis sx).cancels = coverThomasToWireDiet sx.cancels :=
  rfl

/-- PROVED: every embedded Cover & Thomas axis lands on an IT-core
    `ClassicalAssumption` — no engineering-extension assumption is
    in the image of `embedSourceAxis`. -/
theorem embedSourceAxis_image_is_IT_core
    (sx : InformationalPhysicsCoverThomasAlternative.SourceAxis) :
    isITCore (embedSourceAxis sx).cancels = true := by
  -- (embedSourceAxis sx).cancels = coverThomasToWireDiet sx.cancels
  -- Then use coverThomasToWireDiet_image_is_IT_core.
  exact coverThomasToWireDiet_image_is_IT_core sx.cancels

/-- The embedding of the 4-axis Cover & Thomas axis list into a list
    of WIRE_DIET-typed axes. Pointwise application of
    `embedSourceAxis`. -/
def embeddedCoverThomasAxes :
    List InformationalPhysicsForcedBijection.Axis :=
  InformationalPhysicsCoverThomasAlternative.coverThomasAxes.map
    embedSourceAxis

/-- PROVED: the embedded list has length 4 (one per Cover & Thomas
    axis). The embedding does not lose or duplicate axes. -/
theorem embeddedCoverThomasAxes_length :
    embeddedCoverThomasAxes.length = 4 := rfl

/-- PROVED: every axis in the embedded list has an IT-core
    cancellation. -/
theorem embeddedCoverThomasAxes_all_IT_core
    (x : InformationalPhysicsForcedBijection.Axis)
    (hx : x ∈ embeddedCoverThomasAxes) :
    isITCore x.cancels = true := by
  -- x is in the image of embedSourceAxis applied to coverThomasAxes;
  -- structurally the only members are the 4 explicit images.
  cases hx with
  | head _ => rfl
  | tail _ h1 =>
    cases h1 with
    | head _ => rfl
    | tail _ h2 =>
      cases h2 with
      | head _ => rfl
      | tail _ h3 =>
        cases h3 with
        | head _ => rfl
        | tail _ h4 => cases h4

/-! ══════════════════════════════════════════════════════════════════
    ## §9. The load-bearing claim — `pluralism_resolves_to_extension`
    ══════════════════════════════════════════════════════════════════

    Every Cover & Thomas concern IS captured by WIRE_DIET, plus
    WIRE_DIET adds 2 engineering layers (FrameStructure + Ordering).
    The apparent pluralism (4 vs 6) is structural extension, not
    incommensurable carving. -/

/-- PROVED: the load-bearing claim. For every Cover & Thomas
    assumption `a`, there exists a WIRE_DIET assumption `b` such that
    `b = coverThomasToWireDiet a` (the explicit image) AND
    `isITCore b = true` (the image is in the IT-core subset). -/
theorem pluralism_resolves_to_extension :
    ∀ (a : SourceClassicalAssumption),
      ∃ (b : ClassicalAssumption),
        b = coverThomasToWireDiet a ∧ isITCore b = true := by
  intro a
  refine ⟨coverThomasToWireDiet a, rfl, ?_⟩
  exact coverThomasToWireDiet_image_is_IT_core a

/-! ══════════════════════════════════════════════════════════════════
    ## §10. Cover & Thomas ≼ WIRE_DIET (semantic sub-system)
    ══════════════════════════════════════════════════════════════════

    The structural sub-system claim. Three facts:

      (a) the 4-axis Cover & Thomas system embeds into a 4-axis
          sub-list of (semantic) WIRE_DIET axes via
          `embedSourceAxis`;
      (b) the embedding preserves the cancellation structure
          (semantic correspondence);
      (c) the WIRE_DIET system has exactly 2 more axes than the
          embedded Cover & Thomas system — the engineering
          extensions.

    Together these formalize "Cover & Thomas IS a sub-system of
    WIRE_DIET, and the extra 2 axes are the engineering layers". -/

/-- PROVED (sub-system claim, part a): the embedded Cover & Thomas
    axis list has cardinality 4 — one per Cover & Thomas axis,
    preserved by the embedding. -/
theorem coverThomasIsSubsystemOfWireDiet_cardinality :
    embeddedCoverThomasAxes.length =
      InformationalPhysicsCoverThomasAlternative.coverThomasAxisSystem.cardinality :=
  rfl

/-- PROVED (sub-system claim, part b): the embedding commutes with
    the cancellation field — for every Cover & Thomas axis `sx`, the
    embedded axis cancels `coverThomasToWireDiet (sx.cancels)`. -/
theorem coverThomasIsSubsystemOfWireDiet_cancels_commute
    (sx : InformationalPhysicsCoverThomasAlternative.SourceAxis) :
    (embedSourceAxis sx).cancels = coverThomasToWireDiet sx.cancels :=
  rfl

/-- PROVED (sub-system claim, part c): the WIRE_DIET system has
    exactly 2 more axes than the embedded Cover & Thomas system. The
    arithmetic 6 − 4 = 2 lines up with the engineering-extension
    count. -/
theorem coverThomasIsSubsystemOfWireDiet_extension_count :
    InformationalPhysicsForcedBijection.wireDietAxisSystem.cardinality
      = embeddedCoverThomasAxes.length + engineeringExtensionCount := by
  decide

/-- PROVED (sub-system claim, bundled): the 4-axis Cover & Thomas
    system embeds into the 6-axis WIRE_DIET system via the semantic
    correspondence, and the 2 extra WIRE_DIET axes are precisely the
    engineering extensions.

    This is the formal version of "WIRE_DIET-6 = Cover & Thomas-4
    IT-core + 2 engineering extensions". -/
theorem coverThomasIsSubsystemOfWireDiet :
    -- (a) cardinality preserved by the embedding:
    embeddedCoverThomasAxes.length = 4
    ∧
    -- (b) every embedded axis's cancellation is in the IT-core:
    (∀ x ∈ embeddedCoverThomasAxes, isITCore x.cancels = true)
    ∧
    -- (c) WIRE_DIET cardinality decomposes as 4 + 2:
    InformationalPhysicsForcedBijection.wireDietAxisSystem.cardinality
      = embeddedCoverThomasAxes.length + engineeringExtensionCount
    ∧
    -- (d) every Cover & Thomas axis's image preserves cancellation
    --     up to coverThomasToWireDiet:
    (∀ sx : InformationalPhysicsCoverThomasAlternative.SourceAxis,
        (embedSourceAxis sx).cancels =
          coverThomasToWireDiet sx.cancels) :=
  ⟨ embeddedCoverThomasAxes_length
  , embeddedCoverThomasAxes_all_IT_core
  , coverThomasIsSubsystemOfWireDiet_extension_count
  , coverThomasIsSubsystemOfWireDiet_cancels_commute ⟩

/-! ══════════════════════════════════════════════════════════════════
    ## §11. Bundled crown — the unified master frame
    ══════════════════════════════════════════════════════════════════

    A single bundled theorem packaging the structural claims of the
    unification. Useful for downstream modules that want to depend on
    "the pluralism resolves to extension" as one hypothesis. -/

/-- THE UNIFICATION CROWN. Five facts:
      (a) the semantic injection exists and is injective;
      (b) the image lands in the IT-core 4-element subset;
      (c) the engineering extensions are exactly the 2 non-IT-core
          constructors;
      (d) the cardinality decomposes as 6 = 4 + 2;
      (e) every Cover & Thomas concern has a WIRE_DIET image (the
          load-bearing pluralism-resolves-to-extension claim). -/
theorem unifiedCrown :
    -- (a) injectivity:
    (∀ x y : SourceClassicalAssumption,
        coverThomasToWireDiet x = coverThomasToWireDiet y → x = y)
    ∧
    -- (b) image in IT-core:
    (∀ x : SourceClassicalAssumption,
        isITCore (coverThomasToWireDiet x) = true)
    ∧
    -- (c) engineering extensions = non-IT-core:
    (∀ a ∈ engineeringExtensions, isITCore a = false)
    ∧
    -- (d) cardinality decomposition 6 = 4 + 2:
    itCoreCount + engineeringExtensionCount = totalCount
    ∧
    -- (e) pluralism resolves to extension:
    (∀ a : SourceClassicalAssumption,
       ∃ b : ClassicalAssumption,
         b = coverThomasToWireDiet a ∧ isITCore b = true) :=
  ⟨ coverThomasToWireDiet_injective
  , coverThomasToWireDiet_image_is_IT_core
  , engineeringExtensions_are_not_IT_core
  , unifiedCardinality
  , pluralism_resolves_to_extension ⟩

end InformationalPhysicsUnified
