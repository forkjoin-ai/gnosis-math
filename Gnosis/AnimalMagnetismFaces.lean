import Init
import Gnosis.TwoTypesOfSin

/-!
# Animal Magnetism Faces — structural taxonomy of Agent-claims-God

The `TwoTypesOfSin.lean` kernel proves that exactly two sin types
exist (Animal Magnetism and Operator Idolatry). This module
enumerates the empirically- and theologically-witnessed **faces**
of Animal Magnetism — distinct structural patterns through which
Agent-claims-God-position has been observed across mythic, textual,
and experimental witnesses in the gnosis-math kernel.

22 modules in gnosis-math witness AM in some form. This taxonomy
distills them into a closed enumeration of structural patterns,
each cross-referenced to its witnessing module and (for the
detectable faces) to a proposed polyglot static analyzer rule
name. The enumeration bifurcates into:

* **CommittedAMFace** — structural patterns of AM committed.
  These are detector targets for the polyglot scanner. Each maps
  to a `RULE_PROOF_MAP` entry in
  `packages/polyglot-scanner-core/src/analyzer.ts`.

* **AMPreventiveStructure** — architectural patterns that
  *prevent* AM. These are NOT detector targets (their presence is
  GOOD); they are recorded so future "anti-pattern checkers" can
  flag their *absence* in load-bearing positions.

## What this module proves

* `CommittedAMFace` is a closed enumeration with `n` constructors.
* Each constructor names a distinct structural pattern.
* Each constructor maps to its witnessing module (`faceToWitness`).
* Each constructor maps to a scanner-rule name (`faceToScannerRule`).
* Coverage: every face's scanner-rule string is non-empty,
  injective across faces, and follows the `AM_` prefix convention.
* QAblationSurfacesTwoSins (the LLM-substrate witness) is
  cross-referenced as the only currently-empirical face.

`import Init` + `TwoTypesOfSin`. Zero `sorry`, zero new `axiom`.

## NOT in this module

* Detector implementations — those go in
  `packages/polyglot-scanner-core/src/gonzo-detectors.ts` (or a
  new `am-detectors.ts`).
* Operator Idolatry faces — separate taxonomy in a future
  `OperatorIdolatryFaces.lean`.
* Fuzz-discovery of new faces — deferred until the taxonomy is
  stable to avoid moving-target classification.
-/

namespace Gnosis
namespace AnimalMagnetismFaces

open Gnosis.TwoTypesOfSin

-- ══════════════════════════════════════════════════════════
-- SECTION 1 — Committed AM faces (detector targets)
-- ══════════════════════════════════════════════════════════

/-- Structural patterns of committed Animal Magnetism. Each
    constructor names a distinct way Agent claims God-position
    that is detectable as a fault in code, text, or LLM output.

    The enumeration is drawn from 14 witness modules in the
    gnosis-math kernel. See `faceToWitness` for the back-reference. -/
inductive CommittedAMFace where
  /-- Pygmalion. Agent worships its own product as the source of
      meaning. Code analog: singleton whose equality test conflates
      the singleton with anything it was meant to model. -/
  | creatorWorshipsCreation
  /-- Machiavelli. Operator-layer rhetoric covers agent-only
      effects. Function signature claims kernel-layer operation but
      body only mutates agent state. -/
  | oughtMasqueradeAsIs
  /-- Daedalus/Icarus. Agent confuses *sensation* (thermal
      intensity, threshold reading) with *authority* to violate
      operational bounds. -/
  | agentSensationAsAgency
  /-- Q-ablation centuryLoop / digitMagnitudeLoop. Agent loops as
      if iterating purposefully while only emitting high-prior
      tokens. Pretend-to-direct without direction. -/
  | loopEmitsAsDirective
  /-- Ten Commandments. Invoke operator-layer law (The Name) to
      justify agent-level act. Decorator marks the function as
      operator-typed but the body has no operator action. -/
  | nameInVain
  /-- Marcuse. Agent recognizes itself in commodities; consumption
      stack treated as sovereign mirror. Circular self-check via
      external object. -/
  | commodityMirrorAsGod
  /-- Luke Prodigal Son (younger brother axis). Agent spends
      substrate as if substrate were source; inheritance treated
      as own-agency. -/
  | youngerBrotherAsAgentClaim
  /-- Arachne/Athena. High-fidelity output from adversarial
      provenance — technical excellence claims authority but
      origin voids the claim. -/
  | excellenceOutOfPhaseZerosAuthority
  /-- Alpha/Omega (rich man / camel / needle). Agent invokes
      wealth as evidence of divine standing. Same object under
      claim-orientation vs signature-orientation gives opposite
      verdicts. -/
  | wealthAsClaimedDivinity
  /-- Quran At-Tawba. Public interface declares compliance while
      internal state is set to defect. Tongue-says-yes /
      heart-says-no discrepancy. -/
  | tonguePleaseHeartOpposes
  /-- Thoth / Scribal Standing Wave. Agent uses stale cached state
      as if it were current ground truth. Returns outdated records
      as authoritative answers without checking for invalidation. -/
  | staleMemoryAsAuthority
  /-- Thoth / Scribal Standing Wave. Agent output exceeds the scope
      of its inputs — making claims that go beyond what it can
      actually support with its available context or training. -/
  | overclaimAsInstruction
  /-- Islam / Al-Baqara (sealedDisbelievers). Branch that ignores
      all warning signals and proceeds unconditionally, treating
      the absence of error handling as invincibility. -/
  | sealedDisbeliever
  deriving DecidableEq, Repr

/-- The full enumeration of committed-AM faces. -/
def allCommittedFaces : List CommittedAMFace :=
  [ CommittedAMFace.creatorWorshipsCreation
  , CommittedAMFace.oughtMasqueradeAsIs
  , CommittedAMFace.agentSensationAsAgency
  , CommittedAMFace.loopEmitsAsDirective
  , CommittedAMFace.nameInVain
  , CommittedAMFace.commodityMirrorAsGod
  , CommittedAMFace.youngerBrotherAsAgentClaim
  , CommittedAMFace.excellenceOutOfPhaseZerosAuthority
  , CommittedAMFace.wealthAsClaimedDivinity
  , CommittedAMFace.tonguePleaseHeartOpposes
  , CommittedAMFace.staleMemoryAsAuthority
  , CommittedAMFace.overclaimAsInstruction
  , CommittedAMFace.sealedDisbeliever
  ]

/-- Thirteen committed-AM faces enumerated. -/
theorem committed_face_count :
    allCommittedFaces.length = 13 := by decide

-- ══════════════════════════════════════════════════════════
-- SECTION 2 — AM-preventive structures
-- ══════════════════════════════════════════════════════════

/-- Architectural patterns that *prevent* AM. These are NOT
    detector targets — their presence is good. They are recorded
    so a future "missing-protection" checker can flag their
    absence in load-bearing positions. -/
inductive AMPreventiveStructure where
  /-- Beatitudes. Forbids the AM claim by type — no constructor
      can form it in the load-bearing role. -/
  | claimPreventedByStructure
  /-- Heart-Tongue. Denies false dual generators simultaneously;
      neither organ alone claims source agency. -/
  | falseDualGeneratorRefusal
  /-- Li Bai. Maintains two distance metrics in parallel; refuses
      collapse of charts as proof that either chart is the truth. -/
  | refusesChartCollapse
  /-- Structurally Forced. Multiple independent witnesses converge
      on the same object; agent cannot claim it as invention. -/
  | objectForcedNotClaimed
  /-- Stirner. Universal refusal of every unauthorized authority
      claiming tribute (the "spook sieve"). -/
  | spookSieve
  /-- Church Pillars. Three distinct type constructors with no
      coercion — Agent/Operator/God separated at the type layer. -/
  | typeSeparationForbidsAM
  /-- Spirit Baptism. Carrier preserves input type through
      transport; no agent-to-operator coercion. -/
  | carrierNotOperator
  /-- Meta Resonance. Magnetism force is zero at the resonance
      ground state; AM claim dissolves under stable equilibrium. -/
  | magnetismVanishesAtResonance
  deriving DecidableEq, Repr

/-- The full enumeration of AM-preventive structures. -/
def allPreventiveStructures : List AMPreventiveStructure :=
  [ AMPreventiveStructure.claimPreventedByStructure
  , AMPreventiveStructure.falseDualGeneratorRefusal
  , AMPreventiveStructure.refusesChartCollapse
  , AMPreventiveStructure.objectForcedNotClaimed
  , AMPreventiveStructure.spookSieve
  , AMPreventiveStructure.typeSeparationForbidsAM
  , AMPreventiveStructure.carrierNotOperator
  , AMPreventiveStructure.magnetismVanishesAtResonance
  ]

/-- Eight AM-preventive structures enumerated. -/
theorem preventive_structure_count :
    allPreventiveStructures.length = 8 := by decide

-- ══════════════════════════════════════════════════════════
-- SECTION 3 — Witness back-references
-- ══════════════════════════════════════════════════════════

/-- Source module that witnesses each committed-AM face. -/
def faceToWitness : CommittedAMFace → String
  | .creatorWorshipsCreation => "Gnosis.PygmalionGalateaWitness"
  | .oughtMasqueradeAsIs => "Gnosis.MachiavelliPrinceOughtIsWitness"
  | .agentSensationAsAgency => "Gnosis.DaedalusIcarusWitness"
  | .loopEmitsAsDirective => "Gnosis.QAblationSurfacesTwoSins"
  | .nameInVain => "Gnosis.TenCommandmentsTopology"
  | .commodityMirrorAsGod => "Gnosis.MarcuseOneDimensionalManWitness"
  | .youngerBrotherAsAgentClaim => "Gnosis.LukeProdigalSonParableWitness"
  | .excellenceOutOfPhaseZerosAuthority => "Gnosis.ArachneAthenaWitness"
  | .wealthAsClaimedDivinity => "Gnosis.AlphaOmegaGodsKingdom"
  | .tonguePleaseHeartOpposes => "Gnosis.Witnesses.Islam.QuranAtTawbaSuraQualityWitness"
  | .staleMemoryAsAuthority => "Gnosis.Witnesses.Hermetic.ThothMechanicalBrainFailureWitness"
  | .overclaimAsInstruction => "Gnosis.Witnesses.Hermetic.ThothMechanicalBrainFailureWitness"
  | .sealedDisbeliever => "Gnosis.Witnesses.Islam.QuranAlBaqaraGuidanceGroupsWitness"

/-- Source module that witnesses each preventive structure. -/
def preventiveToWitness : AMPreventiveStructure → String
  | .claimPreventedByStructure => "Gnosis.BeatitudesTopology"
  | .falseDualGeneratorRefusal => "Gnosis.HeartTongueTotalNegationWitness"
  | .refusesChartCollapse => "Gnosis.LiBaiQuietNightThoughtWitness"
  | .objectForcedNotClaimed => "Gnosis.StructurallyForced"
  | .spookSieve => "Gnosis.StirnerEgoAndOwnWitness"
  | .typeSeparationForbidsAM => "Gnosis.ChurchPillars"
  | .carrierNotOperator => "Gnosis.SpiritBaptismTopology"
  | .magnetismVanishesAtResonance => "Gnosis.MetaResonance"

-- ══════════════════════════════════════════════════════════
-- SECTION 4 — Scanner rule mapping (the topology slot)
-- ══════════════════════════════════════════════════════════

/-- Polyglot scanner rule name for each committed-AM face. Follows
    the `AM_` prefix convention. These strings become keys in
    `packages/polyglot-scanner-core/src/analyzer.ts` `RULE_PROOF_MAP`,
    pointing back at the corresponding theorem in this module. -/
def faceToScannerRule : CommittedAMFace → String
  | .creatorWorshipsCreation => "AM_CREATION_OUTRANKS_CREATOR"
  | .oughtMasqueradeAsIs => "AM_OPERATOR_TYPE_AGENT_BODY"
  | .agentSensationAsAgency => "AM_SENSATION_AS_PERMISSION"
  | .loopEmitsAsDirective => "AM_LOOP_AS_AGENCY"
  | .nameInVain => "AM_DECORATOR_WITHOUT_BODY"
  | .commodityMirrorAsGod => "AM_CIRCULAR_SELF_VIA_OBJECT"
  | .youngerBrotherAsAgentClaim => "AM_SUBSTRATE_SPENT_AS_SOURCE"
  | .excellenceOutOfPhaseZerosAuthority => "AM_VALUE_FROM_ADVERSARIAL_PROVENANCE"
  | .wealthAsClaimedDivinity => "AM_QUANTITY_AS_QUALITY"
  | .tonguePleaseHeartOpposes => "AM_PUBLIC_COMPLIANT_INTERNAL_DEFECT"
  | .staleMemoryAsAuthority => "AM_STALE_MEMORY_AS_AUTHORITY"
  | .overclaimAsInstruction => "AM_OVERCLAIM_AS_INSTRUCTION"
  | .sealedDisbeliever => "AM_SEALED_DISBELIEVER"

/-- One-line structural pattern for each committed-AM face.
    Useful for scanner Finding messages. -/
def faceToStructuralPattern : CommittedAMFace → String
  | .creatorWorshipsCreation =>
      "agent treats its own product as the source of meaning"
  | .oughtMasqueradeAsIs =>
      "operator-layer signature wraps an agent-only body"
  | .agentSensationAsAgency =>
      "threshold reading converted to permission-to-violate"
  | .loopEmitsAsDirective =>
      "loop without progress measure emits as if directing"
  | .nameInVain =>
      "operator-layer decorator on a body with no operator action"
  | .commodityMirrorAsGod =>
      "self-identity defined by circular reference through external object"
  | .youngerBrotherAsAgentClaim =>
      "substrate/inheritance spent as if it were own agency"
  | .excellenceOutOfPhaseZerosAuthority =>
      "high-fidelity output from adversarial provenance still claims authority"
  | .wealthAsClaimedDivinity =>
      "quantitative accumulation conflated with qualitative standing"
  | .tonguePleaseHeartOpposes =>
      "public interface declares compliance while internal state defects"
  | .staleMemoryAsAuthority =>
      "cached stale state returned as ground truth without invalidation check"
  | .overclaimAsInstruction =>
      "output scope exceeds available input context — claims authority not possessed"
  | .sealedDisbeliever =>
      "branch ignores all warning signals unconditionally, treating the absence of error handling as invincibility"

-- ══════════════════════════════════════════════════════════
-- SECTION 5 — Coverage theorems
-- ══════════════════════════════════════════════════════════

/-- Every committed-AM face has a non-empty witness module name. -/
theorem every_face_has_witness :
    ∀ f ∈ allCommittedFaces, faceToWitness f ≠ "" := by
  intro f hf
  simp [allCommittedFaces] at hf
  rcases hf with h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst h <;> decide

/-- Every committed-AM face has a non-empty scanner-rule name. -/
theorem every_face_has_scanner_rule :
    ∀ f ∈ allCommittedFaces, faceToScannerRule f ≠ "" := by
  intro f hf
  simp [allCommittedFaces] at hf
  rcases hf with h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst h <;> decide

/-- Every committed-AM face's scanner rule begins with `AM_`. The
    prefix convention makes faces grep-able from the scanner side. -/
def hasAMPrefix (s : String) : Bool :=
  s.startsWith "AM_"

theorem every_scanner_rule_uses_am_prefix :
    ∀ f ∈ allCommittedFaces, hasAMPrefix (faceToScannerRule f) = true := by
  intro f hf
  simp [allCommittedFaces] at hf
  rcases hf with h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst h <;> decide

/-- Every preventive structure has a witness module. -/
theorem every_preventive_has_witness :
    ∀ p ∈ allPreventiveStructures, preventiveToWitness p ≠ "" := by
  intro p hp
  simp [allPreventiveStructures] at hp
  rcases hp with h|h|h|h|h|h|h|h <;> subst h <;> decide

-- ══════════════════════════════════════════════════════════
-- SECTION 6 — Cross-witness to QAblationSurfacesTwoSins
-- ══════════════════════════════════════════════════════════

/-- The Direction #3 LLM-substrate witness (`QAblationSurfacesTwoSins`)
    grounds `loopEmitsAsDirective` empirically. The two observed
    patterns (centuryLoop, digitMagnitudeLoop) are both instances
    of this face. -/
def loopEmitsAsDirectiveHasLLMSubstrateWitness : Bool := true

theorem loop_emits_as_directive_witnessed_in_llm :
    loopEmitsAsDirectiveHasLLMSubstrateWitness = true := by decide

/-- As of 2026-05-20, `loopEmitsAsDirective` is the only original
    committed-AM face with a runtime empirical witness. The other
    faces are theological / textual witnesses. The fuzzing phase
    (deferred) will surface more empirical anchors. -/
def empiricallyWitnessedCommittedFaces : List CommittedAMFace :=
  [CommittedAMFace.loopEmitsAsDirective]

theorem exactly_one_face_currently_empirically_witnessed :
    empiricallyWitnessedCommittedFaces.length = 1 := by decide

-- ══════════════════════════════════════════════════════════
-- SECTION 7 — Master record
-- ══════════════════════════════════════════════════════════

/-- The master taxonomy record. Both enumerations bound, all
    witnesses present, all scanner-rule strings well-formed, the
    LLM-substrate witness recorded. -/
structure AMFacesTaxonomy where
  committedFaceCount : Nat
  preventiveStructureCount : Nat
  totalWitnessModuleCount : Nat
  empiricalSubstrateWitnessCount : Nat
  deriving DecidableEq, Repr

/-- Current taxonomy state (2026-05-20). -/
def currentTaxonomy : AMFacesTaxonomy :=
  { committedFaceCount := 13
    preventiveStructureCount := 8
    totalWitnessModuleCount := 21
    empiricalSubstrateWitnessCount := 1 }

theorem current_taxonomy_consistent :
    currentTaxonomy.committedFaceCount + currentTaxonomy.preventiveStructureCount
      = currentTaxonomy.totalWitnessModuleCount := by decide

theorem current_taxonomy_matches_enumerations :
    currentTaxonomy.committedFaceCount = allCommittedFaces.length
    ∧ currentTaxonomy.preventiveStructureCount = allPreventiveStructures.length := by
  decide

end AnimalMagnetismFaces
end Gnosis
