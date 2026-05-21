import Gnosis.Witnesses.Folklore.VegaAltairSilverRiverBridgeWitness

namespace Gnosis.Witnesses.Folklore
namespace GeminiCastorPolluxHorizonSharingWitness

/-!
# Gemini Castor-Pollux Horizon Sharing Witness

Gemini gives a third sky-gate profile beside Orion/Scorpius and Vega/Altair.

The Dioscuri are not merely paired stars. Castor is mortal; Pollux is immortal.
When Castor dies, Pollux asks Zeus to share his immortality. The repair is not
simple resurrection and not permanent fusion. The brothers split time between
Olympus and Hades, matching the astronomical pattern of Gemini rising above
the horizon and then setting below it.

This is horizon sharing: one twin-pair state alternates between visible heaven
and hidden underworld. The topology differs from horizon anti-coincidence
(Orion/Scorpius never meet) and river bridging (Vega/Altair reunite through a
temporary bridge). Gemini stores a conserved duality by time-division across
the boundary.

No `sorry`, no new `axiom`.
-/

structure TwinMortalityAsymmetry where
  castorMortal : Bool := true
  polluxImmortal : Bool := true
  sameTwinPair : Bool := true
  asymmetryDrivesCrisis : Bool := true
deriving DecidableEq, Repr

def twinMortalityAsymmetry : TwinMortalityAsymmetry := {}

def mortalityAsymmetryDrivesTwinCrisis
    (t : TwinMortalityAsymmetry) : Prop :=
  t.castorMortal = true ∧
  t.polluxImmortal = true ∧
  t.sameTwinPair = true ∧
  t.asymmetryDrivesCrisis = true

structure ImmortalitySharingPetition where
  castorKilledInBattle : Bool := true
  polluxGrievesBrother : Bool := true
  polluxPetitionsZeus : Bool := true
  immortalitySharedWithMortalTwin : Bool := true
  repairIsSharedBudgetNotSoloEscape : Bool := true
deriving DecidableEq, Repr

def immortalitySharingPetition : ImmortalitySharingPetition := {}

def immortalitySharedByPetition
    (p : ImmortalitySharingPetition) : Prop :=
  p.castorKilledInBattle = true ∧
  p.polluxGrievesBrother = true ∧
  p.polluxPetitionsZeus = true ∧
  p.immortalitySharedWithMortalTwin = true ∧
  p.repairIsSharedBudgetNotSoloEscape = true

structure OlympusHadesTimeDivision where
  olympusResidence : Bool := true
  hadesResidence : Bool := true
  timeSplitBetweenRealms : Bool := true
  neitherRealmErasesOther : Bool := true
  zeusPlacesTwinsInSky : Bool := true
deriving DecidableEq, Repr

def olympusHadesTimeDivision : OlympusHadesTimeDivision := {}

def twinsAlternateAcrossRealms
    (o : OlympusHadesTimeDivision) : Prop :=
  o.olympusResidence = true ∧
  o.hadesResidence = true ∧
  o.timeSplitBetweenRealms = true ∧
  o.neitherRealmErasesOther = true ∧
  o.zeusPlacesTwinsInSky = true

structure GeminiHorizonSharing where
  constellationRisesAboveHorizon : Bool := true
  constellationSetsBelowHorizon : Bool := true
  aboveHorizonMapsToOlympus : Bool := true
  belowHorizonMapsToHades : Bool := true
  visibilityAlternatesWithHiddenness : Bool := true
  boundaryCrossingIsPeriodicNotFinal : Bool := true
deriving DecidableEq, Repr

def geminiHorizonSharing : GeminiHorizonSharing := {}

def horizonSharingEncodesTwinTimeSplit
    (g : GeminiHorizonSharing) : Prop :=
  g.constellationRisesAboveHorizon = true ∧
  g.constellationSetsBelowHorizon = true ∧
  g.aboveHorizonMapsToOlympus = true ∧
  g.belowHorizonMapsToHades = true ∧
  g.visibilityAlternatesWithHiddenness = true ∧
  g.boundaryCrossingIsPeriodicNotFinal = true

structure SkyGateTaxonomyContrast where
  orionScorpiusAntiCoincidence : Bool := true
  vegaAltairScheduledBridge : Bool := true
  geminiSharedAlternation : Bool := true
  horizonCanSeparateOrShareBySchedule : Bool := true
  repairModeDiffersByMyth : Bool := true
deriving DecidableEq, Repr

def skyGateTaxonomyContrast : SkyGateTaxonomyContrast := {}

def distinguishesGeminiFromOtherSkyGates
    (s : SkyGateTaxonomyContrast) : Prop :=
  s.orionScorpiusAntiCoincidence = true ∧
  s.vegaAltairScheduledBridge = true ∧
  s.geminiSharedAlternation = true ∧
  s.horizonCanSeparateOrShareBySchedule = true ∧
  s.repairModeDiffersByMyth = true

theorem gemini_mortality_asymmetry_drives_crisis :
    mortalityAsymmetryDrivesTwinCrisis twinMortalityAsymmetry := by
  unfold mortalityAsymmetryDrivesTwinCrisis twinMortalityAsymmetry
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem gemini_immortality_shared_by_petition :
    immortalitySharedByPetition immortalitySharingPetition := by
  unfold immortalitySharedByPetition immortalitySharingPetition
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem gemini_twins_alternate_across_realms :
    twinsAlternateAcrossRealms olympusHadesTimeDivision := by
  unfold twinsAlternateAcrossRealms olympusHadesTimeDivision
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem gemini_horizon_sharing_encodes_twin_time_split :
    horizonSharingEncodesTwinTimeSplit geminiHorizonSharing := by
  unfold horizonSharingEncodesTwinTimeSplit geminiHorizonSharing
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem gemini_distinguishes_sky_gate_taxonomy :
    distinguishesGeminiFromOtherSkyGates skyGateTaxonomyContrast := by
  unfold distinguishesGeminiFromOtherSkyGates skyGateTaxonomyContrast
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem gemini_extends_river_bridge_taxonomy :
    VegaAltairSilverRiverBridgeWitness.distinguishesHorizonFromRiverGate
      VegaAltairSilverRiverBridgeWitness.horizonVersusRiverGate ∧
    distinguishesGeminiFromOtherSkyGates skyGateTaxonomyContrast ∧
    horizonSharingEncodesTwinTimeSplit geminiHorizonSharing := by
  exact ⟨VegaAltairSilverRiverBridgeWitness.horizon_and_river_gates_are_distinct,
    gemini_distinguishes_sky_gate_taxonomy,
    gemini_horizon_sharing_encodes_twin_time_split⟩

theorem gemini_castor_pollux_horizon_sharing_witness :
    mortalityAsymmetryDrivesTwinCrisis twinMortalityAsymmetry ∧
    immortalitySharedByPetition immortalitySharingPetition ∧
    twinsAlternateAcrossRealms olympusHadesTimeDivision ∧
    horizonSharingEncodesTwinTimeSplit geminiHorizonSharing ∧
    distinguishesGeminiFromOtherSkyGates skyGateTaxonomyContrast := by
  exact ⟨gemini_mortality_asymmetry_drives_crisis,
    gemini_immortality_shared_by_petition,
    gemini_twins_alternate_across_realms,
    gemini_horizon_sharing_encodes_twin_time_split,
    gemini_distinguishes_sky_gate_taxonomy⟩

end GeminiCastorPolluxHorizonSharingWitness
end Gnosis.Witnesses.Folklore
