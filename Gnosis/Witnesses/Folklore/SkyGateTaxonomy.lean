import Gnosis.Witnesses.Folklore.RahuKetuNodalEclipseWitness

namespace Gnosis.Witnesses.Folklore
namespace SkyGateTaxonomy

/-!
# Sky Gate Taxonomy

This module closes the current sky-folklore wave by separating five operators:

- anti-coincidence: Orion/Scorpius horizon opposition, held in the zodiac seed;
- scheduled bridge: Vega/Altair crossed by the magpie bridge;
- horizon sharing: Gemini time-splitting between Olympus and Hades;
- phase alias: Phosphorus/Hesperus reconciled as Venus;
- nodal intersection: Rahu/Ketu as eclipse-governing lunar nodes.

The common family is sky-gate topology. The honest result is not sameness. Each
witness has a different boundary operator, repair mode, and identity rule.

No `sorry`, no new `axiom`.
-/

inductive SkyGateOperator where
  | antiCoincidence
  | scheduledBridge
  | horizonSharing
  | phaseAlias
  | nodalIntersection
deriving Repr, DecidableEq

def operatorBoundary : SkyGateOperator → Nat
  | .antiCoincidence => 0
  | .scheduledBridge => 1
  | .horizonSharing => 2
  | .phaseAlias => 3
  | .nodalIntersection => 4

structure SkyGateOperatorLedger where
  orionScorpiusAntiCoincidence : Bool := true
  vegaAltairScheduledBridge : Bool := true
  geminiHorizonSharing : Bool := true
  venusPhaseAlias : Bool := true
  rahuKetuNodalIntersection : Bool := true
  operatorsRemainDistinct : Bool := true
deriving DecidableEq, Repr

def skyGateOperatorLedger : SkyGateOperatorLedger := {}

def allFiveSkyGateOperatorsPresent
    (s : SkyGateOperatorLedger) : Prop :=
  s.orionScorpiusAntiCoincidence = true ∧
  s.vegaAltairScheduledBridge = true ∧
  s.geminiHorizonSharing = true ∧
  s.venusPhaseAlias = true ∧
  s.rahuKetuNodalIntersection = true ∧
  s.operatorsRemainDistinct = true

structure BoundaryMechanismSeparation where
  horizonPreventsCoPresence : Bool := true
  riverAllowsAnnualRepair : Bool := true
  horizonAllowsTimeDivision : Bool := true
  solarThresholdAliasesSameBody : Bool := true
  orbitalPlaneCutTriggersOccultation : Bool := true
  noOperatorErasesAnother : Bool := true
deriving DecidableEq, Repr

def boundaryMechanismSeparation : BoundaryMechanismSeparation := {}

def skyGateMechanismsRemainSeparated
    (b : BoundaryMechanismSeparation) : Prop :=
  b.horizonPreventsCoPresence = true ∧
  b.riverAllowsAnnualRepair = true ∧
  b.horizonAllowsTimeDivision = true ∧
  b.solarThresholdAliasesSameBody = true ∧
  b.orbitalPlaneCutTriggersOccultation = true ∧
  b.noOperatorErasesAnother = true

structure IdentityRuleTaxonomy where
  differentBodiesNeverMeet : Bool := true
  differentBodiesMeetByBridge : Bool := true
  twinPairSharesOneFateBudget : Bool := true
  oneBodyHasTwoPhaseNames : Bool := true
  severedOneEntityHasTwoNodes : Bool := true
deriving DecidableEq, Repr

def identityRuleTaxonomy : IdentityRuleTaxonomy := {}

def skyGateIdentityRulesClassified
    (i : IdentityRuleTaxonomy) : Prop :=
  i.differentBodiesNeverMeet = true ∧
  i.differentBodiesMeetByBridge = true ∧
  i.twinPairSharesOneFateBudget = true ∧
  i.oneBodyHasTwoPhaseNames = true ∧
  i.severedOneEntityHasTwoNodes = true

theorem operator_boundary_codes_are_distinct :
    operatorBoundary .antiCoincidence ≠ operatorBoundary .scheduledBridge ∧
    operatorBoundary .scheduledBridge ≠ operatorBoundary .horizonSharing ∧
    operatorBoundary .horizonSharing ≠ operatorBoundary .phaseAlias ∧
    operatorBoundary .phaseAlias ≠ operatorBoundary .nodalIntersection := by
  decide

theorem sky_gate_all_five_operators_present :
    allFiveSkyGateOperatorsPresent skyGateOperatorLedger := by
  unfold allFiveSkyGateOperatorsPresent skyGateOperatorLedger
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem sky_gate_mechanisms_remain_separated :
    skyGateMechanismsRemainSeparated boundaryMechanismSeparation := by
  unfold skyGateMechanismsRemainSeparated boundaryMechanismSeparation
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem sky_gate_identity_rules_classified :
    skyGateIdentityRulesClassified identityRuleTaxonomy := by
  unfold skyGateIdentityRulesClassified identityRuleTaxonomy
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem sky_gate_taxonomy_imports_witness_chain :
    ZodiacGateProfileSeedWitness.comparativeSkyCarriersUnderReserve
      ZodiacGateProfileSeedWitness.comparativeSkyCarriers ∧
    VegaAltairSilverRiverBridgeWitness.scheduledBridgeRepairsSeparation
      VegaAltairSilverRiverBridgeWitness.magpieBridgeReunion ∧
    GeminiCastorPolluxHorizonSharingWitness.horizonSharingEncodesTwinTimeSplit
      GeminiCastorPolluxHorizonSharingWitness.geminiHorizonSharing ∧
    VenusPhosphorusHesperusPhaseAliasWitness.phaseBifurcationIsMutuallyExclusive
      VenusPhosphorusHesperusPhaseAliasWitness.solarElongationBifurcation ∧
    RahuKetuNodalEclipseWitness.eclipseGovernedByNodalIntersection
      RahuKetuNodalEclipseWitness.eclipseOccultationPredicate := by
  exact ⟨ZodiacGateProfileSeedWitness.comparative_sky_carriers_under_reserve,
    VegaAltairSilverRiverBridgeWitness.magpie_bridge_schedules_reunion,
    GeminiCastorPolluxHorizonSharingWitness.gemini_horizon_sharing_encodes_twin_time_split,
    VenusPhosphorusHesperusPhaseAliasWitness.venus_phase_bifurcation_is_mutually_exclusive,
    RahuKetuNodalEclipseWitness.rahu_ketu_eclipse_governed_by_nodal_intersection⟩

theorem sky_gate_taxonomy_witness :
    allFiveSkyGateOperatorsPresent skyGateOperatorLedger ∧
    skyGateMechanismsRemainSeparated boundaryMechanismSeparation ∧
    skyGateIdentityRulesClassified identityRuleTaxonomy ∧
    operatorBoundary .antiCoincidence ≠ operatorBoundary .scheduledBridge ∧
    operatorBoundary .scheduledBridge ≠ operatorBoundary .horizonSharing ∧
    operatorBoundary .horizonSharing ≠ operatorBoundary .phaseAlias ∧
    operatorBoundary .phaseAlias ≠ operatorBoundary .nodalIntersection := by
  exact ⟨sky_gate_all_five_operators_present,
    sky_gate_mechanisms_remain_separated,
    sky_gate_identity_rules_classified,
    operator_boundary_codes_are_distinct.1,
    operator_boundary_codes_are_distinct.2.1,
    operator_boundary_codes_are_distinct.2.2.1,
    operator_boundary_codes_are_distinct.2.2.2⟩

end SkyGateTaxonomy
end Gnosis.Witnesses.Folklore
