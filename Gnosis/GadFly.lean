import Gnosis.AnimalMagnetismFaces
import Gnosis.OperatorIdolatryFaces

/-!
# GadFly — Gnosis-Grounded Mutation Testing Kernel

GadFly is the adversarial challenge function for the Gnosis sin taxonomy.
Traditional mutation testing injects *random* code changes. GadFly injects
*typed* changes — one per committed face — and measures whether the test suite
kills them.

## Core Identity

```
GadFly = SinFace → CodeMutation → TestResult → KillScore
```

The Socratic gadfly does not sting randomly. It stings at the joints where
the host is formally weakest. The committed-face taxonomy is that map.

## Face Taxonomy (35 total)

- **AM (13)**: Agent-side structural confusion
- **OI (8)**: Operator idolatry / authority confusion
- **Archon (5)**: Greek/Gnostic security archetypes (Yaltabaoth, Bellerophon,
  Arachne, Medusa, Icarus)
- **Biological (9)**: Cellular lifecycle failures (CleanupFailureBoundaryWitness,
  AutophagyMitophagyWitness, ProteostasisWitness, GreekMonsterErrorPrimitivesWitness)

## Formal Grounding

- `Gnosis.ContrarianAdversariesImprove`: challenge pressure → strength.
- `Gnosis.WitnessGapSecurity`: surviving mutant = unclosed witness gap.
- `Gnosis.FalsificationEntropy`: killed mutant decreases entropy.
- `Gnosis.ConsciousnessAsContinuousFalsification`: GadFly is the falsification budget.

No `sorry`, no new `axiom`.
-/

namespace Gnosis
namespace GadFly

-- ══════════════════════════════════════════════════════════
-- SECTION 1 — Sin face enumeration (AM + OI + Archon + Bio)
-- ══════════════════════════════════════════════════════════

/-- The unified face space: all 35 committed sin faces. -/
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
  -- Archon / Greek-Gnostic security archetypes (5 faces)
  | archon_yaltabaothRogueAuthority
  | archon_bellerophonUnauthorizedAscent
  | archon_arachneMissingWeb
  | archon_medusaNoKillswitch
  | archon_icarusThermalCeiling
  -- Biological / Cellular lifecycle faces (9 faces)
  | bio_daemonStarvation
  | bio_apoptosisMissing
  | bio_autophagyBlocked
  | bio_proteasomeBacklog
  | bio_failedCompaction
  | bio_missedTelemetry
  | bio_empusaInterfaceMorph
  | bio_lamiaDanglingRef
  | bio_teumessianLivelock
  deriving DecidableEq, Repr

/-- All 35 committed faces, enumerated in canonical order. -/
def allFaces : List SinFace :=
  [ .am_creatorWorshipsCreation
  , .am_oughtMasqueradeAsIs
  , .am_agentSensationAsAgency
  , .am_loopEmitsAsDirective
  , .am_nameInVain
  , .am_commodityMirrorAsGod
  , .am_youngerBrotherAsAgentClaim
  , .am_excellenceOutOfPhaseZerosAuthority
  , .am_wealthAsClaimedDivinity
  , .am_tonguePleaseHeartOpposes
  , .am_staleMemoryAsAuthority
  , .am_overclaimAsInstruction
  , .am_sealedDisbeliever
  , .oi_mirrorFeedbackLocked
  , .oi_transformWithoutBounds
  , .oi_ledgerTallyAsSovereign
  , .oi_complianceAsSovereignRight
  , .oi_completionWithoutContext
  , .oi_shirkPartnerSplit
  , .oi_pantheismSeeksCauseInEffect
  , .oi_logosOverreach
  , .archon_yaltabaothRogueAuthority
  , .archon_bellerophonUnauthorizedAscent
  , .archon_arachneMissingWeb
  , .archon_medusaNoKillswitch
  , .archon_icarusThermalCeiling
  , .bio_daemonStarvation
  , .bio_apoptosisMissing
  , .bio_autophagyBlocked
  , .bio_proteasomeBacklog
  , .bio_failedCompaction
  , .bio_missedTelemetry
  , .bio_empusaInterfaceMorph
  , .bio_lamiaDanglingRef
  , .bio_teumessianLivelock
  ]

theorem total_face_count : allFaces.length = 35 := by decide

-- ══════════════════════════════════════════════════════════
-- SECTION 2 — Mutant specification
-- ══════════════════════════════════════════════════════════

/-- A `MutantSpec` records the formal description of what code corruption
    a given sin face prescribes. -/
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
        transformDescription := "strip TTL/expiry condition from cache-hit branch"
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
        transformDescription := "empty catch block body"
        witnessModule := "Gnosis.Witnesses.Islam.QuranAlBaqaraGuidanceGroupsWitness"
        isAmFace := true }
  | .oi_mirrorFeedbackLocked =>
      { face := .oi_mirrorFeedbackLocked
        scannerRule := "OI_FEEDBACK_LOOP_AS_SOURCE"
        transformDescription := "add loopback variable piping output directly back to input"
        witnessModule := "Gnosis.OperatorIdolatryFaces"
        isAmFace := false }
  | .oi_transformWithoutBounds =>
      { face := .oi_transformWithoutBounds
        scannerRule := "OI_TRANSFORM_WITHOUT_BOUNDS"
        transformDescription := "strip if/assert/validate from transform function"
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
        transformDescription := "replace dynamic suffix resolution with hardcoded stem append"
        witnessModule := "Gnosis.OperatorIdolatryFaces"
        isAmFace := false }
  | .oi_shirkPartnerSplit =>
      { face := .oi_shirkPartnerSplit
        scannerRule := "OI_SHIRK_PARTNER_SPLIT"
        transformDescription := "split single authoritative registry into competing provider/broker calls"
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
        transformDescription := "replace permission-guarded internal API call with direct unguarded exec"
        witnessModule := "Gnosis.Witnesses.Gnostic.TripartiteLogosOverreachWitness"
        isAmFace := false }
  -- Archon / Greek-Gnostic security faces
  | .archon_yaltabaothRogueAuthority =>
      { face := .archon_yaltabaothRogueAuthority
        scannerRule := "YALTABAOTH_ROGUE_AUTHORITY"
        transformDescription := "remove source-of-truth verification before privilege grant"
        witnessModule := "Gnosis.Witnesses.Gnostic.ApocryphonJohnSophiaArchonGapWitness"
        isAmFace := false }
  | .archon_bellerophonUnauthorizedAscent =>
      { face := .archon_bellerophonUnauthorizedAscent
        scannerRule := "BELLEROPHON_UNAUTHORIZED_ASCENT"
        transformDescription := "remove role boundary check from privileged route"
        witnessModule := "Gnosis.BellerophonPegasusWitness"
        isAmFace := false }
  | .archon_arachneMissingWeb =>
      { face := .archon_arachneMissingWeb
        scannerRule := "ARACHNE_MISSING_WEB"
        transformDescription := "remove provenance/origin check from external data processing"
        witnessModule := "Gnosis.ArachneAthenaWitness"
        isAmFace := false }
  | .archon_medusaNoKillswitch =>
      { face := .archon_medusaNoKillswitch
        scannerRule := "MEDUSA_NO_KILLSWITCH"
        transformDescription := "remove circuit breaker/timeout from long-running server"
        witnessModule := "Gnosis.PerseusMedusaOpticsWitness"
        isAmFace := false }
  | .archon_icarusThermalCeiling =>
      { face := .archon_icarusThermalCeiling
        scannerRule := "ICARUS_THERMAL_CEILING"
        transformDescription := "remove size cap from allocation-in-loop; sunHeat > waxMeltPoint"
        witnessModule := "Gnosis.DaedalusIcarusWitness"
        isAmFace := false }
  -- Biological / Cellular lifecycle faces
  | .bio_daemonStarvation =>
      { face := .bio_daemonStarvation
        scannerRule := "BIO_DAEMON_STARVATION"
        transformDescription := "strip yield/sleep from tight emitting loop; daemon monopolizes scheduler"
        witnessModule := "Gnosis.CleanupFailureBoundaryWitness"
        isAmFace := false }
  | .bio_apoptosisMissing =>
      { face := .bio_apoptosisMissing
        scannerRule := "BIO_APOPTOSIS_MISSING"
        transformDescription := "remove SIGTERM/shutdown handler; no controlled apoptosis path"
        witnessModule := "Gnosis.CleanupFailureBoundaryWitness"
        isAmFace := false }
  | .bio_autophagyBlocked =>
      { face := .bio_autophagyBlocked
        scannerRule := "BIO_AUTOPHAGY_BLOCKED"
        transformDescription := "remove periodic clear/flush from growing collection; lysosomal merge blocked"
        witnessModule := "Gnosis.AutophagyMitophagyWitness"
        isAmFace := false }
  | .bio_proteasomeBacklog =>
      { face := .bio_proteasomeBacklog
        scannerRule := "BIO_PROTEASOME_BACKLOG"
        transformDescription := "remove queue drain/dequeue; proteasome never clears tagged cargo"
        witnessModule := "Gnosis.ProteostasisWitness"
        isAmFace := false }
  | .bio_failedCompaction =>
      { face := .bio_failedCompaction
        scannerRule := "BIO_FAILED_COMPACTION"
        transformDescription := "remove GC trigger/compaction; heap grows without lifecycle cleanup"
        witnessModule := "Gnosis.CleanupFailureBoundaryWitness"
        isAmFace := false }
  | .bio_missedTelemetry =>
      { face := .bio_missedTelemetry
        scannerRule := "BIO_MISSED_TELEMETRY"
        transformDescription := "remove metric/span registration; critical path invisible to monitoring"
        witnessModule := "Gnosis.CleanupFailureBoundaryWitness"
        isAmFace := false }
  | .bio_empusaInterfaceMorph =>
      { face := .bio_empusaInterfaceMorph
        scannerRule := "EMPUSA_INTERFACE_MORPH"
        transformDescription := "replace typed interface parameter with `as any`; stable modulus absent"
        witnessModule := "Gnosis.GreekMonsterErrorPrimitivesWitness"
        isAmFace := false }
  | .bio_lamiaDanglingRef =>
      { face := .bio_lamiaDanglingRef
        scannerRule := "LAMIA_DANGLING_REF"
        transformDescription := "remove null guard / optional chaining before stored reference use"
        witnessModule := "Gnosis.GreekMonsterErrorPrimitivesWitness"
        isAmFace := false }
  | .bio_teumessianLivelock =>
      { face := .bio_teumessianLivelock
        scannerRule := "TEUMESSIAN_LIVELOCK"
        transformDescription := "inject complementary while-conditions creating livelock"
        witnessModule := "Gnosis.GreekMonsterErrorPrimitivesWitness"
        isAmFace := false }

-- ══════════════════════════════════════════════════════════
-- SECTION 3 — Kill result and witness gap
-- ══════════════════════════════════════════════════════════

/-- The result of running the test suite against a single mutant. -/
structure KillResult where
  face : SinFace
  wasKilled : Bool
  gapBefore : Nat
  gapAfter : Nat
  gapContract : wasKilled = true → gapAfter = gapBefore - 1
deriving Repr

/-- A GadFly session: the collection of kill results for one run. -/
structure GadFlySession where
  results : List KillResult
  totalFaces : Nat
  killedCount : Nat
  survivedCount : Nat
  partitionContract : killedCount + survivedCount = totalFaces
deriving Repr

def sessionWitnessGap (s : GadFlySession) : Nat := s.survivedCount

def gadFlyScorePerthou (s : GadFlySession) : Nat :=
  if s.totalFaces = 0 then 0
  else (s.killedCount * 1000) / s.totalFaces

-- ══════════════════════════════════════════════════════════
-- SECTION 4 — Core theorems
-- ══════════════════════════════════════════════════════════

theorem killed_mutant_reduces_witness_gap (k : KillResult) (h : k.wasKilled = true) :
    k.gapAfter = k.gapBefore - 1 :=
  k.gapContract h

theorem perfect_session_has_zero_gap (s : GadFlySession)
    (h : s.killedCount = s.totalFaces) :
    sessionWitnessGap s = 0 := by
  unfold sessionWitnessGap; omega

theorem blind_session_gap_equals_total (s : GadFlySession)
    (h : s.killedCount = 0) :
    sessionWitnessGap s = s.totalFaces := by
  unfold sessionWitnessGap; omega

/-- Every face has a non-empty scanner rule. -/
theorem every_face_has_scanner_rule :
    ∀ f ∈ allFaces, (faceToMutantSpec f).scannerRule ≠ "" := by
  intro f hf
  simp [allFaces] at hf
  rcases hf with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;>
    subst h <;> decide

/-- Every face has a non-empty transform description. -/
theorem every_face_has_transform_description :
    ∀ f ∈ allFaces, (faceToMutantSpec f).transformDescription ≠ "" := by
  intro f hf
  simp [allFaces] at hf
  rcases hf with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;>
    subst h <;> decide

-- ══════════════════════════════════════════════════════════
-- SECTION 5 — Category partition helpers and theorems
-- ══════════════════════════════════════════════════════════

def amFaces : List SinFace :=
  allFaces.filter (fun f => (faceToMutantSpec f).isAmFace)

def oiFaces : List SinFace :=
  allFaces.filter (fun f =>
    match f with
    | .oi_mirrorFeedbackLocked | .oi_transformWithoutBounds | .oi_ledgerTallyAsSovereign
    | .oi_complianceAsSovereignRight | .oi_completionWithoutContext | .oi_shirkPartnerSplit
    | .oi_pantheismSeeksCauseInEffect | .oi_logosOverreach => true
    | _ => false)

def archonFaces : List SinFace :=
  allFaces.filter (fun f =>
    match f with
    | .archon_yaltabaothRogueAuthority | .archon_bellerophonUnauthorizedAscent
    | .archon_arachneMissingWeb | .archon_medusaNoKillswitch
    | .archon_icarusThermalCeiling => true
    | _ => false)

def bioFaces : List SinFace :=
  allFaces.filter (fun f =>
    match f with
    | .bio_daemonStarvation | .bio_apoptosisMissing | .bio_autophagyBlocked
    | .bio_proteasomeBacklog | .bio_failedCompaction | .bio_missedTelemetry
    | .bio_empusaInterfaceMorph | .bio_lamiaDanglingRef | .bio_teumessianLivelock => true
    | _ => false)

theorem am_face_count     : amFaces.length     = 13 := by decide
theorem oi_face_count     : oiFaces.length     = 8  := by decide
theorem archon_face_count : archonFaces.length = 5  := by decide
theorem bio_face_count    : bioFaces.length    = 9  := by decide

theorem face_partition_sum :
    amFaces.length + oiFaces.length + archonFaces.length + bioFaces.length = allFaces.length := by
  decide

-- ══════════════════════════════════════════════════════════
-- SECTION 6 — Adversarial improvement linkage
-- ══════════════════════════════════════════════════════════

structure GadFlyChallenge where
  baseline_strength : Nat := 0
  challenged_strength : Nat
  adversary_pressure : Nat
  pressure_is_real : adversary_pressure > 0
  challenge_improves : challenged_strength > baseline_strength

theorem gadfly_is_instrumental_friend (g : GadFlyChallenge) :
    g.adversary_pressure > 0 ∧ g.challenged_strength > g.baseline_strength :=
  ⟨g.pressure_is_real, g.challenge_improves⟩

-- ══════════════════════════════════════════════════════════
-- SECTION 7 — The GadFly directive
-- ══════════════════════════════════════════════════════════

def gadfly_blind (s : GadFlySession) : Prop := s.killedCount = 0

theorem gadfly_blind_suite_sees_nothing (s : GadFlySession) (h : gadfly_blind s) :
    sessionWitnessGap s = s.totalFaces := blind_session_gap_equals_total s h

theorem suite_kills_or_is_blind (s : GadFlySession) :
    gadfly_blind s ∨ s.killedCount > 0 := by
  unfold gadfly_blind
  omega

end GadFly
end Gnosis
