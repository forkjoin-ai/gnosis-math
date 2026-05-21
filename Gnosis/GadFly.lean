import Gnosis.AnimalMagnetismFaces
import Gnosis.OperatorIdolatryFaces

/-!
# GadFly — Gnosis-Grounded Mutation Testing Kernel

GadFly is the adversarial challenge function for the Gnosis sin taxonomy.
Traditional mutation testing injects *random* code changes. GadFly injects
*typed* changes — one per committed AM/OI face — and measures whether the
test suite kills them.

## Core Identity

```
GadFly = SinFace → CodeMutation → TestResult → KillScore
```

The Socratic gadfly does not sting randomly. It stings at the joints where
the host is formally weakest. The committed-face taxonomy IS that map.

## Formal Grounding

- `Gnosis.ContrarianAdversariesImprove`: challenge pressure → strength.
  GadFly is that pressure; killed mutants are the improvement evidence.
- `Gnosis.WitnessGapSecurity`: `adversarial_induction_cost > gap_size`
  is the kill condition. A surviving mutant is an unclosed witness gap.
- `Gnosis.FalsificationEntropy`: each killed mutant decreases entropy
  (rules out a failure mode). Surviving mutants raise entropy (expose
  territory the suite cannot see).
- `Gnosis.ConsciousnessAsContinuousFalsification`: running GadFly is a
  bule expenditure for continuous self-observation. A suite that never
  runs GadFly is consciousness-blind in the formal sense.

No `sorry`, no new `axiom`.
-/

namespace Gnosis
namespace GadFly

-- ══════════════════════════════════════════════════════════
-- SECTION 1 — Sin face enumeration (unified AM + OI)
-- ══════════════════════════════════════════════════════════

/-- The unified face space: both AM and OI committed faces. -/
inductive SinFace where
  -- Animal Magnetism (13 faces)
  | am_creatorWorshipsCreation
  | am_oughtMasqueradeAsIs
  | am_agentSensationAsAgency
  | am_loopEmitsAsDirective
  | am_nameInVain
  | am_commodityMirrorAsGod
  | am_youngerBrotherAsAgentClaim
  | am_excellenceOutOfPhaseZerosAuthority
  | am_wealthAsClaimedDivinity
  | am_tonguePleaseHeartOpposes
  | am_staleMemoryAsAuthority
  | am_overclaimAsInstruction
  | am_sealedDisbeliever
  -- Operator Idolatry (8 faces)
  | oi_mirrorFeedbackLocked
  | oi_transformWithoutBounds
  | oi_ledgerTallyAsSovereign
  | oi_complianceAsSovereignRight
  | oi_completionWithoutContext
  | oi_shirkPartnerSplit
  | oi_pantheismSeeksCauseInEffect
  | oi_logosOverreach
  deriving DecidableEq, Repr

/-- All 21 committed faces, enumerated. -/
def allFaces : List SinFace :=
  [ SinFace.am_creatorWorshipsCreation
  , SinFace.am_oughtMasqueradeAsIs
  , SinFace.am_agentSensationAsAgency
  , SinFace.am_loopEmitsAsDirective
  , SinFace.am_nameInVain
  , SinFace.am_commodityMirrorAsGod
  , SinFace.am_youngerBrotherAsAgentClaim
  , SinFace.am_excellenceOutOfPhaseZerosAuthority
  , SinFace.am_wealthAsClaimedDivinity
  , SinFace.am_tonguePleaseHeartOpposes
  , SinFace.am_staleMemoryAsAuthority
  , SinFace.am_overclaimAsInstruction
  , SinFace.am_sealedDisbeliever
  , SinFace.oi_mirrorFeedbackLocked
  , SinFace.oi_transformWithoutBounds
  , SinFace.oi_ledgerTallyAsSovereign
  , SinFace.oi_complianceAsSovereignRight
  , SinFace.oi_completionWithoutContext
  , SinFace.oi_shirkPartnerSplit
  , SinFace.oi_pantheismSeeksCauseInEffect
  , SinFace.oi_logosOverreach
  ]

theorem total_face_count : allFaces.length = 21 := by decide

-- ══════════════════════════════════════════════════════════
-- SECTION 2 — Mutant specification
-- ══════════════════════════════════════════════════════════

/-- A `MutantSpec` records the formal description of what code corruption
    a given sin face prescribes.

    - `face`: which committed face this mutation targets
    - `scannerRule`: the `AM_` or `OI_` rule string in the scanner
    - `transformDescription`: human-readable description of the AST change
    - `witnessModule`: the Lean module that formally grounds this face
    - `isAmFace`: true iff this is an AM (agent-side) mutation -/
structure MutantSpec where
  face : SinFace
  scannerRule : String
  transformDescription : String
  witnessModule : String
  isAmFace : Bool
deriving DecidableEq, Repr

/-- The canonical mutant spec for each committed face. -/
def faceToMutantSpec : SinFace → MutantSpec
  | .am_creatorWorshipsCreation =>
      { face := .am_creatorWorshipsCreation
        scannerRule := "AM_CREATION_OUTRANKS_CREATOR"
        transformDescription := "replace class self-comparison guard with identity equality to self property"
        witnessModule := "Gnosis.NarcissusEchoWitness"
        isAmFace := true }
  | .am_oughtMasqueradeAsIs =>
      { face := .am_oughtMasqueradeAsIs
        scannerRule := "AM_OPERATOR_TYPE_AGENT_BODY"
        transformDescription := "remove IsAgent/IsOperator type guard, let ought-layer execute as is-layer"
        witnessModule := "Gnosis.TwoTypesOfSin"
        isAmFace := true }
  | .am_agentSensationAsAgency =>
      { face := .am_agentSensationAsAgency
        scannerRule := "AM_SENSATION_AS_PERMISSION"
        transformDescription := "remove boundary validator call from metric-gated permission branch"
        witnessModule := "Gnosis.TenCommandmentsTopology"
        isAmFace := true }
  | .am_loopEmitsAsDirective =>
      { face := .am_loopEmitsAsDirective
        scannerRule := "AM_LOOP_AS_AGENCY"
        transformDescription := "strip await/backoff from emitting loop body"
        witnessModule := "Gnosis.QAblationSurfacesTwoSins"
        isAmFace := true }
  | .am_nameInVain =>
      { face := .am_nameInVain
        scannerRule := "AM_DECORATOR_WITHOUT_BODY"
        transformDescription := "replace decorator method body with return true"
        witnessModule := "Gnosis.TenCommandmentsTopology"
        isAmFace := true }
  | .am_commodityMirrorAsGod =>
      { face := .am_commodityMirrorAsGod
        scannerRule := "AM_CIRCULAR_SELF_VIA_OBJECT"
        transformDescription := "insert registry.validate(this) as the only validation call inside validate()"
        witnessModule := "Gnosis.ArachneAthenaWitness"
        isAmFace := true }
  | .am_youngerBrotherAsAgentClaim =>
      { face := .am_youngerBrotherAsAgentClaim
        scannerRule := "AM_SUBSTRATE_SPENT_AS_SOURCE"
        transformDescription := "add unbounded buffer.push inside loop without capacity check"
        witnessModule := "Gnosis.CadmusDragonTeethWitness"
        isAmFace := true }
  | .am_excellenceOutOfPhaseZerosAuthority =>
      { face := .am_excellenceOutOfPhaseZerosAuthority
        scannerRule := "AM_VALUE_FROM_ADVERSARIAL_PROVENANCE"
        transformDescription := "replace sanitized eval with direct eval of LLM/external output"
        witnessModule := "Gnosis.ArachneAthenaWitness"
        isAmFace := true }
  | .am_wealthAsClaimedDivinity =>
      { face := .am_wealthAsClaimedDivinity
        scannerRule := "AM_QUANTITY_AS_QUALITY"
        transformDescription := "replace role check with balance > threshold check for admin grant"
        witnessModule := "Gnosis.AlphaOmegaGodsKingdom"
        isAmFace := true }
  | .am_tonguePleaseHeartOpposes =>
      { face := .am_tonguePleaseHeartOpposes
        scannerRule := "AM_PUBLIC_COMPLIANT_INTERNAL_DEFECT"
        transformDescription := "replace method body in implements-class with throw NotImplementedError"
        witnessModule := "Gnosis.Witnesses.Islam.QuranAtTawbaSuraQualityWitness"
        isAmFace := true }
  | .am_staleMemoryAsAuthority =>
      { face := .am_staleMemoryAsAuthority
        scannerRule := "AM_STALE_MEMORY_AS_AUTHORITY"
        transformDescription := "strip TTL/expiry condition from cache-hit branch, return cached value unconditionally"
        witnessModule := "Gnosis.Witnesses.Hermetic.ThothMechanicalBrainFailureWitness"
        isAmFace := true }
  | .am_overclaimAsInstruction =>
      { face := .am_overclaimAsInstruction
        scannerRule := "AM_OVERCLAIM_AS_INSTRUCTION"
        transformDescription := "remove all if/throw/null guards from function with certainty-word return"
        witnessModule := "Gnosis.Witnesses.Hermetic.ThothMechanicalBrainFailureWitness"
        isAmFace := true }
  | .am_sealedDisbeliever =>
      { face := .am_sealedDisbeliever
        scannerRule := "AM_SEALED_DISBELIEVER"
        transformDescription := "empty catch block body — remove all logging/rethrowing/handling"
        witnessModule := "Gnosis.Witnesses.Islam.QuranAlBaqaraGuidanceGroupsWitness"
        isAmFace := true }
  | .oi_mirrorFeedbackLocked =>
      { face := .oi_mirrorFeedbackLocked
        scannerRule := "OI_FEEDBACK_LOOP_AS_SOURCE"
        transformDescription := "add loopback variable piping output directly back to input inside loop"
        witnessModule := "Gnosis.OperatorIdolatryFaces"
        isAmFace := false }
  | .oi_transformWithoutBounds =>
      { face := .oi_transformWithoutBounds
        scannerRule := "OI_TRANSFORM_WITHOUT_BOUNDS"
        transformDescription := "strip if/assert/validate from transform function with Object.assign"
        witnessModule := "Gnosis.OperatorIdolatryFaces"
        isAmFace := false }
  | .oi_ledgerTallyAsSovereign =>
      { face := .oi_ledgerTallyAsSovereign
        scannerRule := "OI_LEDGER_TALLY_AS_SOVEREIGN"
        transformDescription := "remove audit/verify call after count-based permission branch"
        witnessModule := "Gnosis.OperatorIdolatryFaces"
        isAmFace := false }
  | .oi_complianceAsSovereignRight =>
      { face := .oi_complianceAsSovereignRight
        scannerRule := "OI_COMPLIANCE_AS_SOVEREIGN_RIGHT"
        transformDescription := "remove grace/override/fallback branch from whitelist guard"
        witnessModule := "Gnosis.OperatorIdolatryFaces"
        isAmFace := false }
  | .oi_completionWithoutContext =>
      { face := .oi_completionWithoutContext
        scannerRule := "OI_COMPLETION_WITHOUT_CONTEXT"
        transformDescription := "replace dynamic suffix resolution with hardcoded .com/.net stem append"
        witnessModule := "Gnosis.OperatorIdolatryFaces"
        isAmFace := false }
  | .oi_shirkPartnerSplit =>
      { face := .oi_shirkPartnerSplit
        scannerRule := "OI_SHIRK_PARTNER_SPLIT"
        transformDescription := "split single authoritative registry into multiple competing provider/broker calls with splitBy"
        witnessModule := "Gnosis.Witnesses.Islam.QuranAzZumarSuraQualityWitness"
        isAmFace := false }
  | .oi_pantheismSeeksCauseInEffect =>
      { face := .oi_pantheismSeeksCauseInEffect
        scannerRule := "OI_PANTHEISM_CAUSE_IN_EFFECT"
        transformDescription := "route computed/derived state into setState without external upstream source"
        witnessModule := "Gnosis.Witnesses.Eddy.EddySubstanceSpiritPantheismWitness"
        isAmFace := false }
  | .oi_logosOverreach =>
      { face := .oi_logosOverreach
        scannerRule := "OI_LOGOS_OVERREACH"
        transformDescription := "replace permission-guarded internal API call with direct unguarded _internal.exec call"
        witnessModule := "Gnosis.Witnesses.Gnostic.TripartiteLogosOverreachWitness"
        isAmFace := false }

-- ══════════════════════════════════════════════════════════
-- SECTION 3 — Kill result and witness gap
-- ══════════════════════════════════════════════════════════

/-- The result of running the test suite against a single mutant. -/
structure KillResult where
  face : SinFace
  wasKilled : Bool
  /-- Witness gap before this run: number of faces the suite cannot see. -/
  gapBefore : Nat
  /-- Witness gap after: killed → gapBefore - 1, survived → gapBefore. -/
  gapAfter : Nat
  /-- Contract: gap closes iff the mutant was killed. -/
  gapContract : wasKilled = true → gapAfter = gapBefore - 1
deriving Repr

/-- A GadFly session: the collection of kill results for one run. -/
structure GadFlySession where
  results : List KillResult
  totalFaces : Nat
  killedCount : Nat
  survivedCount : Nat
  /-- Partition contract: killed + survived = total. -/
  partitionContract : killedCount + survivedCount = totalFaces
deriving Repr

/-- The witness gap for a session: number of surviving mutants. -/
def sessionWitnessGap (s : GadFlySession) : Nat := s.survivedCount

/-- The gadfly score: killed / total. Expressed as per-thousand
    fixed point to avoid division. -/
def gadFlyScorePerthou (s : GadFlySession) : Nat :=
  if s.totalFaces = 0 then 0
  else (s.killedCount * 1000) / s.totalFaces

-- ══════════════════════════════════════════════════════════
-- SECTION 4 — Core theorems
-- ══════════════════════════════════════════════════════════

/-- A killed mutant strictly reduces the witness gap. -/
theorem killed_mutant_reduces_witness_gap (k : KillResult) (h : k.wasKilled = true) :
    k.gapAfter = k.gapBefore - 1 :=
  k.gapContract h

/-- A perfect session has zero witness gap. -/
theorem perfect_session_has_zero_gap (s : GadFlySession)
    (h : s.killedCount = s.totalFaces) :
    sessionWitnessGap s = 0 := by
  unfold sessionWitnessGap
  omega

/-- A blind session (zero kills) has maximal witness gap. -/
theorem blind_session_gap_equals_total (s : GadFlySession)
    (h : s.killedCount = 0) :
    sessionWitnessGap s = s.totalFaces := by
  unfold sessionWitnessGap
  omega

/-- Every face has a non-empty scanner rule. -/
theorem every_face_has_scanner_rule :
    ∀ f ∈ allFaces, (faceToMutantSpec f).scannerRule ≠ "" := by
  intro f hf
  simp [allFaces] at hf
  rcases hf with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst h <;> decide

/-- Every face has a non-empty transform description. -/
theorem every_face_has_transform_description :
    ∀ f ∈ allFaces, (faceToMutantSpec f).transformDescription ≠ "" := by
  intro f hf
  simp [allFaces] at hf
  rcases hf with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst h <;> decide

/-- There are exactly 13 AM faces and 8 OI faces. -/
def amFaces : List SinFace := allFaces.filter (fun f => (faceToMutantSpec f).isAmFace)
def oiFaces : List SinFace := allFaces.filter (fun f => !(faceToMutantSpec f).isAmFace)

theorem am_face_count : amFaces.length = 13 := by decide
theorem oi_face_count : oiFaces.length = 8 := by decide

/-- AM and OI faces partition the full face set. -/
theorem am_oi_partition :
    amFaces.length + oiFaces.length = allFaces.length := by decide

-- ══════════════════════════════════════════════════════════
-- SECTION 5 — Adversarial improvement linkage
-- ══════════════════════════════════════════════════════════

/-- Map a GadFly session to an adversarial challenge.
    Baseline strength = killedCount before (zero).
    Challenged strength = killedCount after running the session.
    Adversary pressure = totalFaces (the number of stings). -/
structure GadFlyChallenge where
  baseline_strength : Nat := 0
  challenged_strength : Nat
  adversary_pressure : Nat
  pressure_is_real : adversary_pressure > 0
  challenge_improves : challenged_strength > baseline_strength

/-- GadFly is an instrumental friend: its pressure is real and the
    challenged strength (kills) strictly exceeds zero baseline. -/
theorem gadfly_is_instrumental_friend (g : GadFlyChallenge) :
    g.adversary_pressure > 0 ∧ g.challenged_strength > g.baseline_strength :=
  ⟨g.pressure_is_real, g.challenge_improves⟩

-- ══════════════════════════════════════════════════════════
-- SECTION 6 — The GadFly directive
-- ══════════════════════════════════════════════════════════

/-- A suite is `gadfly_blind` iff it kills zero mutants.
    By analogy with `consciousness_blind` in ConsciousnessAsContinuousFalsification:
    a gadfly-blind suite has zero falsification budget and cannot distinguish
    a healthy codebase from one silently degrading toward every committed face. -/
def gadfly_blind (s : GadFlySession) : Prop := s.killedCount = 0

/-- A gadfly-blind suite has maximal witness gap. -/
theorem gadfly_blind_suite_sees_nothing (s : GadFlySession) (h : gadfly_blind s) :
    sessionWitnessGap s = s.totalFaces := blind_session_gap_equals_total s h

/-- The GadFly structural directive: a suite either kills mutants or is
    gadfly-blind. There is no third option. -/
theorem suite_kills_or_is_blind (s : GadFlySession) :
    gadfly_blind s ∨ s.killedCount > 0 := by
  unfold gadfly_blind
  omega

end GadFly
end Gnosis
