import Gnosis.Witnesses.Folklore.AriesInitiationSparkWitness

namespace Gnosis.Witnesses.Folklore
namespace TaurusMaterialStabilizationWitness

/-!
# Taurus Material Stabilization Witness

Taurus upgrades the second zodiac scaffold operator from personality stereotype
to structural function: material stabilization after Aries ignition.

The bull carrier slows and grounds raw kinetic force. In the Europa/white-bull
complex, the bull carries across the sea into geographic settlement; in the
Cretan/Marathon bull complex, dangerous animal force must be captured,
contained, or redirected before a city can remain stable. Taurus therefore maps
to preservation, embodied weight, sensory continuity, and physical security.

If Aries is the launch vector, Taurus is the anchoring mass that lets the
result persist.

No `sorry`, no new `axiom`.
-/

structure BullStabilizationCarrier where
  kineticImpulseCaptured : Bool := true
  geographicSettlementFounded : Bool := true
  sensoryPreservationEnforced : Bool := true
  inertiaBecomesStructuralWeight : Bool := true
  rawForceGroundedIntoMatter : Bool := true
deriving DecidableEq, Repr

def bullStabilizationCarrier : BullStabilizationCarrier := {}

def bullGroundsKineticImpulse
    (b : BullStabilizationCarrier) : Prop :=
  b.kineticImpulseCaptured = true ∧
  b.geographicSettlementFounded = true ∧
  b.sensoryPreservationEnforced = true ∧
  b.inertiaBecomesStructuralWeight = true ∧
  b.rawForceGroundedIntoMatter = true

structure EuropaSeaSettlement where
  whiteBullCarriesAcrossSea : Bool := true
  crossingEndsInCreteAnchor : Bool := true
  motionConvertsToPlace : Bool := true
  desireBecomesDynasticSettlement : Bool := true
  seaTransitRequiresMaterialLanding : Bool := true
deriving DecidableEq, Repr

def europaSeaSettlement : EuropaSeaSettlement := {}

def europaTransitAnchorsGeography
    (e : EuropaSeaSettlement) : Prop :=
  e.whiteBullCarriesAcrossSea = true ∧
  e.crossingEndsInCreteAnchor = true ∧
  e.motionConvertsToPlace = true ∧
  e.desireBecomesDynasticSettlement = true ∧
  e.seaTransitRequiresMaterialLanding = true

structure BullContainmentWork where
  dangerousBullForceNamed : Bool := true
  captureOrContainmentRequired : Bool := true
  cityStabilityDependsOnGrounding : Bool := true
  uncontrolledKinesisThreatensOrder : Bool := true
  preservedStrengthBecomesAsset : Bool := true
deriving DecidableEq, Repr

def bullContainmentWork : BullContainmentWork := {}

def bullContainmentStabilizesCity
    (c : BullContainmentWork) : Prop :=
  c.dangerousBullForceNamed = true ∧
  c.captureOrContainmentRequired = true ∧
  c.cityStabilityDependsOnGrounding = true ∧
  c.uncontrolledKinesisThreatensOrder = true ∧
  c.preservedStrengthBecomesAsset = true

structure TaurusOperatorUpgrade where
  zodiacOperatorIsMaterialStabilization : Bool := true
  scaffoldUpgradedByBullCarrier : Bool := true
  ariesImpulseReceivesMass : Bool := true
  physicalSecurityCompoundsOverTime : Bool := true
  sourceReserveStillHeld : Bool := true
  notReducedToStubbornnessStereotype : Bool := true
deriving DecidableEq, Repr

def taurusOperatorUpgrade : TaurusOperatorUpgrade := {}

def taurusUpgradesMaterialStabilizationOperator
    (t : TaurusOperatorUpgrade) : Prop :=
  t.zodiacOperatorIsMaterialStabilization = true ∧
  t.scaffoldUpgradedByBullCarrier = true ∧
  t.ariesImpulseReceivesMass = true ∧
  t.physicalSecurityCompoundsOverTime = true ∧
  t.sourceReserveStillHeld = true ∧
  t.notReducedToStubbornnessStereotype = true

theorem taurus_bull_grounds_kinetic_impulse :
    bullGroundsKineticImpulse bullStabilizationCarrier := by
  unfold bullGroundsKineticImpulse bullStabilizationCarrier
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem taurus_europa_transit_anchors_geography :
    europaTransitAnchorsGeography europaSeaSettlement := by
  unfold europaTransitAnchorsGeography europaSeaSettlement
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem taurus_bull_containment_stabilizes_city :
    bullContainmentStabilizesCity bullContainmentWork := by
  unfold bullContainmentStabilizesCity bullContainmentWork
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem taurus_upgrades_material_stabilization_operator :
    taurusUpgradesMaterialStabilizationOperator taurusOperatorUpgrade := by
  unfold taurusUpgradesMaterialStabilizationOperator taurusOperatorUpgrade
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem taurus_imports_twelvefold_operator_anchor :
    ZodiacTwelvefoldOperatorSystemWitness.signOperator
      ZodiacTwelvefoldOperatorSystemWitness.ZodiacSign.taurus =
        ZodiacTwelvefoldOperatorSystemWitness.ZodiacOperator.materialStabilization ∧
    AriesInitiationSparkWitness.ramCarriesInitiationSpark
      AriesInitiationSparkWitness.ramInitiationCarrier ∧
    taurusUpgradesMaterialStabilizationOperator taurusOperatorUpgrade := by
  exact ⟨rfl,
    AriesInitiationSparkWitness.aries_ram_carries_initiation_spark,
    taurus_upgrades_material_stabilization_operator⟩

theorem taurus_material_stabilization_witness :
    bullGroundsKineticImpulse bullStabilizationCarrier ∧
    europaTransitAnchorsGeography europaSeaSettlement ∧
    bullContainmentStabilizesCity bullContainmentWork ∧
    taurusUpgradesMaterialStabilizationOperator taurusOperatorUpgrade := by
  exact ⟨taurus_bull_grounds_kinetic_impulse,
    taurus_europa_transit_anchors_geography,
    taurus_bull_containment_stabilizes_city,
    taurus_upgrades_material_stabilization_operator⟩

end TaurusMaterialStabilizationWitness
end Gnosis.Witnesses.Folklore
