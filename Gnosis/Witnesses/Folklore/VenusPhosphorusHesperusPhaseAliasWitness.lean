import Gnosis.Witnesses.Folklore.GeminiCastorPolluxHorizonSharingWitness

namespace Gnosis.Witnesses.Folklore
namespace VenusPhosphorusHesperusPhaseAliasWitness

/-!
# Venus Phosphorus-Hesperus Phase Alias Witness

Not every cosmic duality has two bodies.

Greek dawn/dusk star language personified the morning appearance of Venus as
Phosphorus, the light-bringer before the Sun, and the evening appearance as
Hesperus, the star after sunset. The old reading treated them as two celestial
heralds because the same wanderer appeared at opposite solar thresholds.
Pythagorean reconciliation collapses the aliases: the two named phases track
one planet, Venus.

This differs from the other sky-gates in this folder. Orion/Scorpius separates
different bodies by horizon anti-coincidence. Vega/Altair separates different
bodies by the Silver River and repairs the split by bridge. Gemini shares a
pair's fate by alternating above and below the horizon. Venus stores a same-body
duality: dawn and dusk are phase aliases of one moving carrier.

No `sorry`, no new `axiom`.
-/

structure DawnDuskAliasLedger where
  phosphorusMorningName : Bool := true
  hesperusEveningName : Bool := true
  dawnHeraldsSun : Bool := true
  duskFollowsSunBelowHorizon : Bool := true
  twoNamesBeforeReconciliation : Bool := true
deriving DecidableEq, Repr

def dawnDuskAliasLedger : DawnDuskAliasLedger := {}

def dawnDuskAliasesSplitVenus
    (d : DawnDuskAliasLedger) : Prop :=
  d.phosphorusMorningName = true ∧
  d.hesperusEveningName = true ∧
  d.dawnHeraldsSun = true ∧
  d.duskFollowsSunBelowHorizon = true ∧
  d.twoNamesBeforeReconciliation = true

structure SingleWandererReconciliation where
  venusSinglePlanet : Bool := true
  morningAndEveningSameBody : Bool := true
  pythagoreanIdentityProof : Bool := true
  dualHeraldsCollapseToPhaseExpressions : Bool := true
  identityDoesNotEraseDawnDuskRoles : Bool := true
deriving DecidableEq, Repr

def singleWandererReconciliation : SingleWandererReconciliation := {}

def reconcilesAliasesAsOneWanderer
    (s : SingleWandererReconciliation) : Prop :=
  s.venusSinglePlanet = true ∧
  s.morningAndEveningSameBody = true ∧
  s.pythagoreanIdentityProof = true ∧
  s.dualHeraldsCollapseToPhaseExpressions = true ∧
  s.identityDoesNotEraseDawnDuskRoles = true

structure SameBodyPhaseDuality where
  oneCarrierTwoAppearances : Bool := true
  beginningPhaseAtDawn : Bool := true
  endingPhaseAtDusk : Bool := true
  observationalAliasBeforeOrbitModel : Bool := true
  phaseDifferenceNotObjectDifference : Bool := true
deriving DecidableEq, Repr

def sameBodyPhaseDuality : SameBodyPhaseDuality := {}

def sameBodyCarriesTwoThresholdPhases
    (p : SameBodyPhaseDuality) : Prop :=
  p.oneCarrierTwoAppearances = true ∧
  p.beginningPhaseAtDawn = true ∧
  p.endingPhaseAtDusk = true ∧
  p.observationalAliasBeforeOrbitModel = true ∧
  p.phaseDifferenceNotObjectDifference = true

structure SolarElongationBifurcation where
  heliocentricInnerOrbit : Bool := true
  morningApparitionPrecedesDawn : Bool := true
  eveningApparitionFollowsDusk : Bool := true
  simultaneousThresholdRoleImpossible : Bool := true
  identityConservedAcrossExclusivePhases : Bool := true
deriving DecidableEq, Repr

def solarElongationBifurcation : SolarElongationBifurcation := {}

def phaseBifurcationIsMutuallyExclusive
    (e : SolarElongationBifurcation) : Prop :=
  e.heliocentricInnerOrbit = true ∧
  e.morningApparitionPrecedesDawn = true ∧
  e.eveningApparitionFollowsDusk = true ∧
  e.simultaneousThresholdRoleImpossible = true ∧
  e.identityConservedAcrossExclusivePhases = true

structure SkyDualityTaxonomyExtension where
  separatedBodiesByHorizon : Bool := true
  separatedBodiesByRiverBridge : Bool := true
  pairedBodiesBySharedTimeSplit : Bool := true
  sameBodyByPhaseAlias : Bool := true
  identityProofIsDifferentFromBridgeOrAlternation : Bool := true
deriving DecidableEq, Repr

def skyDualityTaxonomyExtension : SkyDualityTaxonomyExtension := {}

def extendsSkyDualityTaxonomy
    (t : SkyDualityTaxonomyExtension) : Prop :=
  t.separatedBodiesByHorizon = true ∧
  t.separatedBodiesByRiverBridge = true ∧
  t.pairedBodiesBySharedTimeSplit = true ∧
  t.sameBodyByPhaseAlias = true ∧
  t.identityProofIsDifferentFromBridgeOrAlternation = true

theorem venus_dawn_dusk_aliases_split :
    dawnDuskAliasesSplitVenus dawnDuskAliasLedger := by
  unfold dawnDuskAliasesSplitVenus dawnDuskAliasLedger
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem venus_aliases_reconciled_as_one_wanderer :
    reconcilesAliasesAsOneWanderer singleWandererReconciliation := by
  unfold reconcilesAliasesAsOneWanderer singleWandererReconciliation
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem venus_same_body_carries_two_threshold_phases :
    sameBodyCarriesTwoThresholdPhases sameBodyPhaseDuality := by
  unfold sameBodyCarriesTwoThresholdPhases sameBodyPhaseDuality
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem venus_phase_bifurcation_is_mutually_exclusive :
    phaseBifurcationIsMutuallyExclusive solarElongationBifurcation := by
  unfold phaseBifurcationIsMutuallyExclusive solarElongationBifurcation
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem venus_extends_sky_duality_taxonomy :
    extendsSkyDualityTaxonomy skyDualityTaxonomyExtension := by
  unfold extendsSkyDualityTaxonomy skyDualityTaxonomyExtension
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem venus_extends_gemini_horizon_taxonomy :
    GeminiCastorPolluxHorizonSharingWitness.distinguishesGeminiFromOtherSkyGates
      GeminiCastorPolluxHorizonSharingWitness.skyGateTaxonomyContrast ∧
    sameBodyCarriesTwoThresholdPhases sameBodyPhaseDuality ∧
    phaseBifurcationIsMutuallyExclusive solarElongationBifurcation ∧
    extendsSkyDualityTaxonomy skyDualityTaxonomyExtension := by
  exact ⟨GeminiCastorPolluxHorizonSharingWitness.gemini_distinguishes_sky_gate_taxonomy,
    venus_same_body_carries_two_threshold_phases,
    venus_phase_bifurcation_is_mutually_exclusive,
    venus_extends_sky_duality_taxonomy⟩

theorem venus_phosphorus_hesperus_phase_alias_witness :
    dawnDuskAliasesSplitVenus dawnDuskAliasLedger ∧
    reconcilesAliasesAsOneWanderer singleWandererReconciliation ∧
    sameBodyCarriesTwoThresholdPhases sameBodyPhaseDuality ∧
    phaseBifurcationIsMutuallyExclusive solarElongationBifurcation ∧
    extendsSkyDualityTaxonomy skyDualityTaxonomyExtension := by
  exact ⟨venus_dawn_dusk_aliases_split,
    venus_aliases_reconciled_as_one_wanderer,
    venus_same_body_carries_two_threshold_phases,
    venus_phase_bifurcation_is_mutually_exclusive,
    venus_extends_sky_duality_taxonomy⟩

end VenusPhosphorusHesperusPhaseAliasWitness
end Gnosis.Witnesses.Folklore
