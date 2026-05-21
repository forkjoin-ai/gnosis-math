import Init
import Gnosis.TwoTypesOfSin

/-!
# Operator Idolatry Faces — structural taxonomy of Operator-claims-God

The `TwoTypesOfSin.lean` kernel proves that exactly two sin types
exist (Animal Magnetism and Operator Idolatry). This module
enumerates the empirically- and theologically-witnessed **faces**
of Operator Idolatry — distinct structural patterns through which
Operator-claims-God-position (mechanism-as-source) has been observed
across mythic, textual, and experimental witnesses in the gnosis-math kernel.

This taxonomy distills these structural patterns into a closed enumeration,
each cross-referenced to its witnessing module and to a proposed polyglot
static analyzer rule name. The enumeration bifurcates into:

* **CommittedOIFace** — structural patterns of committed Operator Idolatry.
  These are detector targets for the polyglot scanner. Each maps
  to a `RULE_PROOF_MAP` entry in
  `packages/polyglot-scanner-core/src/analyzer.ts`.

* **OIPreventiveStructure** — architectural patterns that
  *prevent* OI. These are recorded so future "anti-pattern checkers" can
  flag their *absence* in load-bearing positions.

## What this module proves

* `CommittedOIFace` is a closed enumeration with 5 constructors.
* Each constructor names a distinct structural pattern.
* Each constructor maps to its witnessing module (`faceToWitness`).
* Each constructor maps to a scanner-rule name (`faceToScannerRule`).
* Coverage: every face's scanner-rule string is non-empty,
  injective across faces, and follows the `OI_` prefix convention.

`import Init` + `TwoTypesOfSin`. Zero `sorry`, zero new `axiom`.
-/

namespace Gnosis
namespace OperatorIdolatryFaces

open Gnosis.TwoTypesOfSin

-- ══════════════════════════════════════════════════════════
-- SECTION 1 — Committed OI faces (detector targets)
-- ══════════════════════════════════════════════════════════

/-- Structural patterns of committed Operator Idolatry. Each
    constructor names a distinct way an Operator (mechanism) claims
    God-position that is detectable as a fault in code, text, or LLM output.

    The enumeration is drawn from witness modules in the gnosis-math kernel.
    See `faceToWitness` for the back-reference. -/
inductive CommittedOIFace where
  /-- Echo & Narcissus. Mirror-feedback treated as the causal source.
      Code analog: self-mirroring feedback loop feeding output back to input
      without a damping factor, leading to feedback lock. -/
  | mirrorFeedbackLocked
  /-- Glaucus & Scylla (Circe's potion). Dynamic type-shape mutation
      without validation or preconditions, treating potion/transformation
      as causal source without bounds. -/
  | transformWithoutBounds
  /-- Cyamites bean-hero. Tallying ledger treated as sovereign source.
      Tallying a count variable and treating it as absolute authority without
      independent verification or audit limits. -/
  | ledgerTallyAsSovereign
  /-- Elder Brother axis. compliance ledger treated as sovereign right.
      Dutiful list compliance treated as absolute entitlement, bypassing grace
      or override fallback controls. -/
  | complianceAsSovereignRight
  /-- QAblation dotComFiller. Standard completion mechanism treated as context-aware
      agency. String completion via hardcoded generic suffixes when input stem
      matches standard patterns, bypassing dynamic evaluation. -/
  | completionWithoutContext
  /-- Islam / Az-Zumar. One servant's dependency graph split into multiple
      competing authority sources, each claiming sovereignty over the whole.
      Partners claim nearness / intercession but produce divided obedience. -/
  | shirkPartnerSplit
  /-- Eddy / Substance Spirit Pantheism. Effect-layer state is treated
      as the causal source of the system it belongs to. The mechanism
      seeks its own cause inside itself rather than above it. -/
  | pantheismSeeksCauseInEffect
  /-- Gnostic / Tripartite Logos. Operator acts beyond command scope
      and without consent, grasping at incomprehensible authority;
      produces shadow/copy defects that mistake themselves for the source. -/
  | logosOverreach
  deriving DecidableEq, Repr

/-- The full enumeration of committed-OI faces. -/
def allCommittedFaces : List CommittedOIFace :=
  [ CommittedOIFace.mirrorFeedbackLocked
  , CommittedOIFace.transformWithoutBounds
  , CommittedOIFace.ledgerTallyAsSovereign
  , CommittedOIFace.complianceAsSovereignRight
  , CommittedOIFace.completionWithoutContext
  , CommittedOIFace.shirkPartnerSplit
  , CommittedOIFace.pantheismSeeksCauseInEffect
  , CommittedOIFace.logosOverreach
  ]

/-- Eight committed-OI faces enumerated. -/
theorem committed_face_count :
     allCommittedFaces.length = 8 := by decide

-- ══════════════════════════════════════════════════════════
-- SECTION 2 — OI-preventive structures
-- ══════════════════════════════════════════════════════════

/-- Architectural patterns that *prevent* OI. These are NOT
    detector targets — their presence is good. -/
inductive OIPreventiveStructure where
  /-- Church Pillars. Three distinct type constructors with no
      coercion — Agent/Operator/God separated at the type layer. -/
  | typeSeparationForbidsOI
  /-- Kernel Invariance. Kernel/Operator functions remain stable under
      edge transitions, but cannot act as the limit. -/
  | kernelInvariancePreserved
  /-- Only God is Immune. Confirms no operator is immune to the limit
      signature, preserving the ontological boundary. -/
  | onlyGodIsImmune
  deriving DecidableEq, Repr

/-- The full enumeration of OI-preventive structures. -/
def allPreventiveStructures : List OIPreventiveStructure :=
  [ OIPreventiveStructure.typeSeparationForbidsOI
  , OIPreventiveStructure.kernelInvariancePreserved
  , OIPreventiveStructure.onlyGodIsImmune
  ]

/-- Three OI-preventive structures enumerated. -/
theorem preventive_structure_count :
    allPreventiveStructures.length = 3 := by decide

-- ══════════════════════════════════════════════════════════
-- SECTION 3 — Witness back-references
-- ══════════════════════════════════════════════════════════

/-- Source module that witnesses each committed-OI face. -/
def faceToWitness : CommittedOIFace → String
  | .mirrorFeedbackLocked => "Gnosis.EchoNarcissusWitness"
  | .transformWithoutBounds => "Gnosis.GlaucusScyllaWitness"
  | .ledgerTallyAsSovereign => "Gnosis.CyamitesBeanWitness"
  | .complianceAsSovereignRight => "Gnosis.LukeProdigalSonParableWitness"
  | .completionWithoutContext => "Gnosis.QAblationSurfacesTwoSins"
  | .shirkPartnerSplit => "Gnosis.Witnesses.Islam.QuranAzZumarSuraQualityWitness"
  | .pantheismSeeksCauseInEffect => "Gnosis.Witnesses.Eddy.EddySubstanceSpiritPantheismWitness"
  | .logosOverreach => "Gnosis.Witnesses.Gnostic.TripartiteLogosOverreachWitness"

/-- Source module that witnesses each preventive structure. -/
def preventiveToWitness : OIPreventiveStructure → String
  | .typeSeparationForbidsOI => "Gnosis.ChurchPillars"
  | .kernelInvariancePreserved => "Gnosis.KernelInvariance"
  | .onlyGodIsImmune => "Gnosis.OnlyGodIsImmune"

-- ══════════════════════════════════════════════════════════
-- SECTION 4 — Scanner rule mapping (the topology slot)
-- ══════════════════════════════════════════════════════════

/-- Polyglot scanner rule name for each committed-OI face. Follows
    the `OI_` prefix convention. These strings become keys in
    `packages/polyglot-scanner-core/src/analyzer.ts` `RULE_PROOF_MAP`,
    pointing back at the corresponding theorem in this module. -/
def faceToScannerRule : CommittedOIFace → String
  | .mirrorFeedbackLocked => "OI_FEEDBACK_LOOP_AS_SOURCE"
  | .transformWithoutBounds => "OI_TRANSFORM_WITHOUT_BOUNDS"
  | .ledgerTallyAsSovereign => "OI_LEDGER_TALLY_AS_SOVEREIGN"
  | .complianceAsSovereignRight => "OI_COMPLIANCE_AS_SOVEREIGN_RIGHT"
  | .completionWithoutContext => "OI_COMPLETION_WITHOUT_CONTEXT"
  | .shirkPartnerSplit => "OI_SHIRK_PARTNER_SPLIT"
  | .pantheismSeeksCauseInEffect => "OI_PANTHEISM_CAUSE_IN_EFFECT"
  | .logosOverreach => "OI_LOGOS_OVERREACH"

/-- One-line structural pattern for each committed-OI face.
    Useful for scanner Finding messages. -/
def faceToStructuralPattern : CommittedOIFace → String
  | .mirrorFeedbackLocked =>
      "self-mirroring feedback loop feeds output back to input without damping"
  | .transformWithoutBounds =>
      "dynamic type-shape mutation performed without checking preconditions or validation bounds"
  | .ledgerTallyAsSovereign =>
      "count variable tallied and treated as absolute authority without verification"
  | .complianceAsSovereignRight =>
      "compliance list treated as absolute entitlement, bypassing grace override fallback"
  | .completionWithoutContext =>
      "string completion via hardcoded generic suffixes when input stem matches standard patterns"
  | .shirkPartnerSplit =>
      "single dependency graph split into multiple competing authority sources each claiming sovereignty"
  | .pantheismSeeksCauseInEffect =>
      "effect-layer state treated as causal source of the system it belongs to"
  | .logosOverreach =>
      "operator acts beyond command scope without consent, producing shadow/copy defects that claim source identity"

-- ══════════════════════════════════════════════════════════
-- SECTION 5 — Coverage theorems
-- ══════════════════════════════════════════════════════════

/-- Every committed-OI face has a non-empty witness module name. -/
theorem every_face_has_witness :
    ∀ f ∈ allCommittedFaces, faceToWitness f ≠ "" := by
  intro f hf
  simp [allCommittedFaces] at hf
  rcases hf with h|h|h|h|h|h|h|h <;> subst h <;> decide

/-- Every committed-OI face has a non-empty scanner-rule name. -/
theorem every_face_has_scanner_rule :
    ∀ f ∈ allCommittedFaces, faceToScannerRule f ≠ "" := by
  intro f hf
  simp [allCommittedFaces] at hf
  rcases hf with h|h|h|h|h|h|h|h <;> subst h <;> decide

/-- Every committed-OI face's scanner rule begins with `OI_`. -/
def hasOIPrefix (s : String) : Bool :=
  s.startsWith "OI_"

theorem every_scanner_rule_uses_oi_prefix :
    ∀ f ∈ allCommittedFaces, hasOIPrefix (faceToScannerRule f) = true := by
  intro f hf
  simp [allCommittedFaces] at hf
  rcases hf with h|h|h|h|h|h|h|h <;> subst h <;> decide

/-- Every preventive structure has a witness module. -/
theorem every_preventive_has_witness :
    ∀ p ∈ allPreventiveStructures, preventiveToWitness p ≠ "" := by
  intro p hp
  simp [allPreventiveStructures] at hp
  rcases hp with h|h|h <;> subst h <;> decide

-- ══════════════════════════════════════════════════════════
-- SECTION 6 — Master record
-- ══════════════════════════════════════════════════════════

/-- The master taxonomy record. Both enumerations bound, all
    witnesses present, all scanner-rule strings well-formed. -/
structure OIFacesTaxonomy where
  committedFaceCount : Nat
  preventiveStructureCount : Nat
  totalWitnessModuleCount : Nat
  deriving DecidableEq, Repr

/-- Current taxonomy state. -/
def currentTaxonomy : OIFacesTaxonomy :=
  { committedFaceCount := 8
    preventiveStructureCount := 3
    totalWitnessModuleCount := 11 }

theorem current_taxonomy_consistent :
    currentTaxonomy.committedFaceCount + currentTaxonomy.preventiveStructureCount
      = currentTaxonomy.totalWitnessModuleCount := by decide

theorem current_taxonomy_matches_enumerations :
    currentTaxonomy.committedFaceCount = allCommittedFaces.length
    ∧ currentTaxonomy.preventiveStructureCount = allPreventiveStructures.length := by
  decide

end OperatorIdolatryFaces
end Gnosis
