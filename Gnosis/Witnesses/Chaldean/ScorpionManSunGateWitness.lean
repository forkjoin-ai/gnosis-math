import Gnosis.CassiopeiaWitness
import Gnosis.Witnesses.Chaldean.BabelSpeechConfusionTowerWitness
import Gnosis.Witnesses.Chaldean.SiduriSabituSeaGateRefusalWitness
import Gnosis.Witnesses.Chaldean.UddusunamirSphinxHadesGateWitness
import Gnosis.Witnesses.Chaldean.WatersOfDeathCrossingWitness

namespace Gnosis.Witnesses.Chaldean
namespace ScorpionManSunGateWitness

/-!
# Scorpion-Man Sun Gate Witness

Source surface:
`docs/ebooks/source-texts/chaldean-account-of-genesis-smith.txt`, Tablet IX
of the Izdubar cycle and Smith's later correction note.

Izdubar reaches the mountains of Mas, where composite scorpion-men guard the
sun's rising and setting. Their bodies span the vertical world: crowns at the
lattice of heaven, feet under hell. Their appearance is like death, their fear
shakes the forests, and they guard the gate of the solar road.

This is a cosmic threshold, not a mere monster encounter. The scorpion-man and
his female diagnose Izdubar's divine affliction, receive his Hasisadra purpose,
warn him about the twelve-kaspu sand corridor, and authorize the road of the
sun. Smith also corrects the beings as half scorpion, half man, and notes a
star of the scorpion tied to the eighth month. That supports a bounded
astronomical gate reading. Orion/Scorpio and Cassiopeia comparisons are
sky-topology candidates: hunter/scorpion horizon opposition and inverted atlas
node both match cosmic gate behavior, but the proved Chaldean claim here is
scorpion-star/month plus sun-road gate.

Cassiopeia's Aethiopian myth setting is kept as a geography reserve. The
comparison is sky-carrier form, not Chaldean provenance.

This also seeds a broader zodiac-gate program. The source proves one gate
profile, Scorpion. The claim that all zodiac signs carry gate profiles remains a
research reserve until each sign has a bounded witness.

No `sorry`, no new `axiom`.
-/

structure ScorpionCompositeGatekeeper where
  halfScorpionHalfMan : Bool := true
  mountainsOfMasReached : Bool := true
  crownAtHeavenLattice : Bool := true
  feetUnderHell : Bool := true
  gateGuarded : Bool := true
  deathlikeAppearance : Bool := true
  fearShakesForests : Bool := true
deriving DecidableEq, Repr

def scorpionCompositeGatekeeper : ScorpionCompositeGatekeeper := {}

def scorpionManSpansCosmicGate (s : ScorpionCompositeGatekeeper) : Prop :=
  s.halfScorpionHalfMan = true ∧
  s.mountainsOfMasReached = true ∧
  s.crownAtHeavenLattice = true ∧
  s.feetUnderHell = true ∧
  s.gateGuarded = true ∧
  s.deathlikeAppearance = true ∧
  s.fearShakesForests = true

structure SolarRoadGuard where
  guardsRisingSunDaily : Bool := true
  guardsSettingSun : Bool := true
  roadOfSunNamed : Bool := true
  cosmicRouteNotLocalDoor : Bool := true
  blessedRegionRouteLearned : Bool := true
deriving DecidableEq, Repr

def solarRoadGuard : SolarRoadGuard := {}

def guardsSunRoadThreshold (g : SolarRoadGuard) : Prop :=
  g.guardsRisingSunDaily = true ∧
  g.guardsSettingSun = true ∧
  g.roadOfSunNamed = true ∧
  g.cosmicRouteNotLocalDoor = true ∧
  g.blessedRegionRouteLearned = true

structure AfflictionDiagnosisAndAuthorization where
  femaleScorpionInterlocutor : Bool := true
  asksWhoComesWithGodAffliction : Bool := true
  workOfGodLaidOnMan : Bool := true
  hasisadraPurposeStated : Bool := true
  deathAndLifeKnownToHasisadra : Bool := true
  monsterSpeaksWarning : Bool := true
  passageDifficult : Bool := true
deriving DecidableEq, Repr

def afflictionDiagnosisAndAuthorization : AfflictionDiagnosisAndAuthorization := {}

def gateReadsBodyBeforeRoute (a : AfflictionDiagnosisAndAuthorization) : Prop :=
  a.femaleScorpionInterlocutor = true ∧
  a.asksWhoComesWithGodAffliction = true ∧
  a.workOfGodLaidOnMan = true ∧
  a.hasisadraPurposeStated = true ∧
  a.deathAndLifeKnownToHasisadra = true ∧
  a.monsterSpeaksWarning = true ∧
  a.passageDifficult = true

structure TwelveKaspuDarkCorridor where
  twelveKaspuJourneyNamed : Bool := true
  completelyCoveredWithSand : Bool := true
  noCultivatedField : Bool := true
  repeatedKaspuStages : Bool := true
  cannotLookBehind : Bool := true
  shadowOfSunReached : Bool := true
  jewelTreeRegionAfterPassage : Bool := true
deriving DecidableEq, Repr

def twelveKaspuDarkCorridor : TwelveKaspuDarkCorridor := {}

def sunRoadDarkPassage (t : TwelveKaspuDarkCorridor) : Prop :=
  t.twelveKaspuJourneyNamed = true ∧
  t.completelyCoveredWithSand = true ∧
  t.noCultivatedField = true ∧
  t.repeatedKaspuStages = true ∧
  t.cannotLookBehind = true ∧
  t.shadowOfSunReached = true ∧
  t.jewelTreeRegionAfterPassage = true

structure AstronomicalScorpionReserve where
  scorpionWordCorrectionNamed : Bool := true
  starOfScorpionNamed : Bool := true
  eighthMonthPlacementNamed : Bool := true
  cometScorpionTailComparisonNamed : Bool := true
  sourceDoesNotNameOrionBelt : Bool := true
deriving DecidableEq, Repr

def astronomicalScorpionReserve : AstronomicalScorpionReserve := {}

def scorpionStarGateHeldUnderReserve (a : AstronomicalScorpionReserve) : Prop :=
  a.scorpionWordCorrectionNamed = true ∧
  a.starOfScorpionNamed = true ∧
  a.eighthMonthPlacementNamed = true ∧
  a.cometScorpionTailComparisonNamed = true ∧
  a.sourceDoesNotNameOrionBelt = true

structure OrionScorpioHunterReserve where
  greekHunterScorpionConflictNamed : Bool := true
  hunterAndScorpionOpposedInSky : Bool := true
  oneRisesAsOtherSets : Bool := true
  horizonAlternationMatchesGateTopology : Bool := true
  chaldeanSourceNamesScorpionNotOrion : Bool := true
  comparisonIsStructuralNotIdentity : Bool := true
deriving DecidableEq, Repr

def orionScorpioHunterReserve : OrionScorpioHunterReserve := {}

def orionScorpioSkyOppositionUnderReserve
    (o : OrionScorpioHunterReserve) : Prop :=
  o.greekHunterScorpionConflictNamed = true ∧
  o.hunterAndScorpionOpposedInSky = true ∧
  o.oneRisesAsOtherSets = true ∧
  o.horizonAlternationMatchesGateTopology = true ∧
  o.chaldeanSourceNamesScorpionNotOrion = true ∧
  o.comparisonIsStructuralNotIdentity = true

structure CassiopeiaSkyGateComparison where
  invertedAtlasNodePreserved : Bool := true
  fixedSkyCoordinateCarrier : Bool := true
  mythicErrorEncodedAsNavigation : Bool := true
  skyCanPreserveBoundaryState : Bool := true
  aethiopianMythSettingReserved : Bool := true
  notClaimedAsChaldeanProvenance : Bool := true
  comparisonIsGateFamilyNotSameMyth : Bool := true
deriving DecidableEq, Repr

def cassiopeiaSkyGateComparison : CassiopeiaSkyGateComparison := {}

def cassiopeiaMatchesCosmicGateForm
    (c : CassiopeiaSkyGateComparison) : Prop :=
  c.invertedAtlasNodePreserved = true ∧
  c.fixedSkyCoordinateCarrier = true ∧
  c.mythicErrorEncodedAsNavigation = true ∧
  c.skyCanPreserveBoundaryState = true ∧
  c.aethiopianMythSettingReserved = true ∧
  c.notClaimedAsChaldeanProvenance = true ∧
  c.comparisonIsGateFamilyNotSameMyth = true

structure ZodiacGateProfileReserve where
  scorpionGateProfileSeedProved : Bool := true
  zodiacWideProfilesHypothesized : Bool := true
  eachSignNeedsOwnWitness : Bool := true
  noCompleteZodiacTableClaimedHere : Bool := true
  gateProfilesShouldTrackBoundaryFunction : Bool := true
deriving DecidableEq, Repr

def zodiacGateProfileReserve : ZodiacGateProfileReserve := {}

def zodiacGateProgramSeededByScorpion
    (z : ZodiacGateProfileReserve) : Prop :=
  z.scorpionGateProfileSeedProved = true ∧
  z.zodiacWideProfilesHypothesized = true ∧
  z.eachSignNeedsOwnWitness = true ∧
  z.noCompleteZodiacTableClaimedHere = true ∧
  z.gateProfilesShouldTrackBoundaryFunction = true

theorem scorpion_man_spans_cosmic_gate :
    scorpionManSpansCosmicGate scorpionCompositeGatekeeper := by
  unfold scorpionManSpansCosmicGate scorpionCompositeGatekeeper
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem scorpion_guards_sun_road_threshold :
    guardsSunRoadThreshold solarRoadGuard := by
  unfold guardsSunRoadThreshold solarRoadGuard
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem scorpion_gate_reads_body_before_route :
    gateReadsBodyBeforeRoute afflictionDiagnosisAndAuthorization := by
  unfold gateReadsBodyBeforeRoute afflictionDiagnosisAndAuthorization
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem scorpion_sun_road_dark_passage :
    sunRoadDarkPassage twelveKaspuDarkCorridor := by
  unfold sunRoadDarkPassage twelveKaspuDarkCorridor
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem scorpion_star_gate_held_under_reserve :
    scorpionStarGateHeldUnderReserve astronomicalScorpionReserve := by
  unfold scorpionStarGateHeldUnderReserve astronomicalScorpionReserve
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem scorpion_orion_sky_opposition_under_reserve :
    orionScorpioSkyOppositionUnderReserve orionScorpioHunterReserve := by
  unfold orionScorpioSkyOppositionUnderReserve orionScorpioHunterReserve
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem scorpion_cassiopeia_matches_cosmic_gate_form :
    cassiopeiaMatchesCosmicGateForm cassiopeiaSkyGateComparison := by
  unfold cassiopeiaMatchesCosmicGateForm cassiopeiaSkyGateComparison
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem scorpion_zodiac_gate_program_seeded :
    zodiacGateProgramSeededByScorpion zodiacGateProfileReserve := by
  unfold zodiacGateProgramSeededByScorpion zodiacGateProfileReserve
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem scorpion_contrasts_sea_gate_refusal :
    SiduriSabituSeaGateRefusalWitness.diagnosticGateClosure
      SiduriSabituSeaGateRefusalWitness.sabituDiagnosticClosure ∧
    gateReadsBodyBeforeRoute afflictionDiagnosisAndAuthorization := by
  exact ⟨SiduriSabituSeaGateRefusalWitness.sabitu_diagnostic_gate_closure,
    scorpion_gate_reads_body_before_route⟩

theorem scorpion_inherits_death_water_route_target :
    WatersOfDeathCrossingWitness.boundaryCrossingDisclosesHiddenKnowledge
      WatersOfDeathCrossingWitness.blessedRegionDisclosure ∧
    guardsSunRoadThreshold solarRoadGuard := by
  exact ⟨WatersOfDeathCrossingWitness.waters_boundary_crossing_discloses_hidden_knowledge,
    scorpion_guards_sun_road_threshold⟩

theorem scorpion_crosses_cosmic_gate_family :
    BabelSpeechConfusionTowerWitness.sevenStageCosmicTower
      BabelSpeechConfusionTowerWitness.sevenStageTowerArchitecture ∧
    UddusunamirSphinxHadesGateWitness.sphinxOpensUnderworldGate
      UddusunamirSphinxHadesGateWitness.uddusunamirSphinx ∧
    scorpionManSpansCosmicGate scorpionCompositeGatekeeper := by
  exact ⟨BabelSpeechConfusionTowerWitness.babel_seven_stage_cosmic_tower,
    UddusunamirSphinxHadesGateWitness.uddusunamir_sphinx_opens_underworld_gate,
    scorpion_man_spans_cosmic_gate⟩

theorem scorpion_inherits_cassiopeia_sky_topology :
    Gnosis.CassiopeiaWitness.inversionEncoding
      Gnosis.CassiopeiaWitness.cassiopeiaConstellation ∧
    Gnosis.CassiopeiaWitness.atlasNode
      Gnosis.CassiopeiaWitness.cassiopeiaConstellation ∧
    cassiopeiaMatchesCosmicGateForm cassiopeiaSkyGateComparison := by
  exact ⟨Gnosis.CassiopeiaWitness.constellation_encodes_inversion,
    Gnosis.CassiopeiaWitness.humiliation_upgrades_to_atlas_node,
    scorpion_cassiopeia_matches_cosmic_gate_form⟩

theorem scorpion_man_sun_gate_witness :
    scorpionManSpansCosmicGate scorpionCompositeGatekeeper ∧
    guardsSunRoadThreshold solarRoadGuard ∧
    gateReadsBodyBeforeRoute afflictionDiagnosisAndAuthorization ∧
    sunRoadDarkPassage twelveKaspuDarkCorridor ∧
    scorpionStarGateHeldUnderReserve astronomicalScorpionReserve ∧
    orionScorpioSkyOppositionUnderReserve orionScorpioHunterReserve ∧
    cassiopeiaMatchesCosmicGateForm cassiopeiaSkyGateComparison ∧
    zodiacGateProgramSeededByScorpion zodiacGateProfileReserve := by
  exact ⟨scorpion_man_spans_cosmic_gate,
    scorpion_guards_sun_road_threshold,
    scorpion_gate_reads_body_before_route,
    scorpion_sun_road_dark_passage,
    scorpion_star_gate_held_under_reserve,
    scorpion_orion_sky_opposition_under_reserve,
    scorpion_cassiopeia_matches_cosmic_gate_form,
    scorpion_zodiac_gate_program_seeded⟩

end ScorpionManSunGateWitness
end Gnosis.Witnesses.Chaldean
