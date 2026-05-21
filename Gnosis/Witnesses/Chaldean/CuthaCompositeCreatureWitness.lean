import Gnosis.GreekMonsterErrorPrimitivesWitness
import Gnosis.Witnesses.Chaldean.MummuTiamatuWaterChaosCarrierWitness

namespace Gnosis.Witnesses.Chaldean
namespace CuthaCompositeCreatureWitness

/-!
# Cutha Composite Creature Witness

Source surface:
`docs/ebooks/source-texts/chaldean-account-of-genesis-smith.txt`, Chapter VI,
opening discussion, Cutha tablet, and beginning of the Seven Wicked Spirits
tablet.

Chapter VI shifts from one creation series to a variant-tradition graph. Smith
states that the creation accounts were traditions, repeated orally before
writing, and therefore varied by period and place. The Cutha tablet is not a
minor duplicate. It gives a different cosmogonic surface: turbid waters rather
than pure water, composite bird/raven/human bodies, Tiamat/Tamat giving
strength and life, seven brother-kings with a large people, destruction cycles,
future-king inscription logic, and then a neighboring seven-spirit pattern with
storm, wind, abyss, moon distress, and Hea/Merodach repair.

The topology is variant cosmogony as branch coverage. Composite beings are not
noise to discard; they are boundary creatures that preserve the places where
the carrier has not resolved into a single clean type. This mirrors the monster
error-primitives work: hybrid bodies and wicked spirits mark runtime boundary
conditions.

No `sorry`, no new `axiom`.
-/

structure VariantTraditionBranch where
  oralTraditionsVaryByPeriod : Bool := true
  relatedStoriesCommittedToWriting : Bool := true
  berosusDiffersFromCuneiformSeries : Bool := true
  cuthaTabletPreservesAnotherVersion : Bool := true
  branchCoverageBeatsSingleStoryFlattening : Bool := true
deriving DecidableEq, Repr

def variantTraditionBranch : VariantTraditionBranch := {}

def variantCosmogonyBranch (v : VariantTraditionBranch) : Prop :=
  v.oralTraditionsVaryByPeriod = true ∧
  v.relatedStoriesCommittedToWriting = true ∧
  v.berosusDiffersFromCuneiformSeries = true ∧
  v.cuthaTabletPreservesAnotherVersion = true ∧
  v.branchCoverageBeatsSingleStoryFlattening = true

structure CuthaWaterCreatureLayer where
  turbidWaterDrunkPureWaterRefused : Bool := true
  nothingWrittenAndEarthSterile : Bool := true
  birdBodiesWithHumanBeingStatus : Bool := true
  ravenFacesNamed : Bool := true
  earthDwellingCreatedForThem : Bool := true
deriving DecidableEq, Repr

def cuthaWaterCreatureLayer : CuthaWaterCreatureLayer := {}

def turbidCompositeCreatureLayer (c : CuthaWaterCreatureLayer) : Prop :=
  c.turbidWaterDrunkPureWaterRefused = true ∧
  c.nothingWrittenAndEarthSterile = true ∧
  c.birdBodiesWithHumanBeingStatus = true ∧
  c.ravenFacesNamed = true ∧
  c.earthDwellingCreatedForThem = true

structure TiamatStrengthTransmission where
  tamatGivesStrength : Bool := true
  mistressOfGodsRaisesLife : Bool := true
  creaturesGrowInEarthMidst : Bool := true
  sevenBrotherKingsNamed : Bool := true
  sixThousandPeopleCounted : Bool := true
deriving DecidableEq, Repr

def tiamatStrengthTransmission : TiamatStrengthTransmission := {}

def tiamatLifeStrengthCarrier (t : TiamatStrengthTransmission) : Prop :=
  t.tamatGivesStrength = true ∧
  t.mistressOfGodsRaisesLife = true ∧
  t.creaturesGrowInEarthMidst = true ∧
  t.sevenBrotherKingsNamed = true ∧
  t.sixThousandPeopleCounted = true

structure DestructionAndFutureKingLedger where
  massExpeditionsDoNotReturn : Bool := true
  corpsesAndWasteRemain : Bool := true
  peopleSavedFromNightDeathSpiritsCurses : Bool := true
  tabletDepositedAtCuthaNergalTemple : Bool := true
  futureKingWarnedToReadAndNotTurnAway : Bool := true
deriving DecidableEq, Repr

def destructionAndFutureKingLedger : DestructionAndFutureKingLedger := {}

def cuthaDestructionLedger (d : DestructionAndFutureKingLedger) : Prop :=
  d.massExpeditionsDoNotReturn = true ∧
  d.corpsesAndWasteRemain = true ∧
  d.peopleSavedFromNightDeathSpiritsCurses = true ∧
  d.tabletDepositedAtCuthaNergalTemple = true ∧
  d.futureKingWarnedToReadAndNotTurnAway = true

structure SevenSpiritStormBoundary where
  sevenRebelSpiritsNamed : Bool := true
  animalSerpentAndEvilWindForms : Bool := true
  violentWindAndTempestAttached : Bool := true
  descendToAbyssOfWaters : Bool := true
  heaMerodachRepairRouteOpens : Bool := true
deriving DecidableEq, Repr

def sevenSpiritStormBoundary : SevenSpiritStormBoundary := {}

def sevenSpiritBoundaryWitness (s : SevenSpiritStormBoundary) : Prop :=
  s.sevenRebelSpiritsNamed = true ∧
  s.animalSerpentAndEvilWindForms = true ∧
  s.violentWindAndTempestAttached = true ∧
  s.descendToAbyssOfWaters = true ∧
  s.heaMerodachRepairRouteOpens = true

theorem cutha_variant_cosmogony_branch :
    variantCosmogonyBranch variantTraditionBranch := by
  unfold variantCosmogonyBranch variantTraditionBranch
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem cutha_turbid_composite_creature_layer :
    turbidCompositeCreatureLayer cuthaWaterCreatureLayer := by
  unfold turbidCompositeCreatureLayer cuthaWaterCreatureLayer
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem cutha_tiamat_life_strength_carrier :
    tiamatLifeStrengthCarrier tiamatStrengthTransmission := by
  unfold tiamatLifeStrengthCarrier tiamatStrengthTransmission
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem cutha_destruction_ledger :
    cuthaDestructionLedger destructionAndFutureKingLedger := by
  unfold cuthaDestructionLedger destructionAndFutureKingLedger
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem cutha_seven_spirit_boundary :
    sevenSpiritBoundaryWitness sevenSpiritStormBoundary := by
  unfold sevenSpiritBoundaryWitness sevenSpiritStormBoundary
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem cutha_inherits_tiamat_water_carrier :
    MummuTiamatuWaterChaosCarrierWitness.mummuTiamatuCarriesOrigin
      MummuTiamatuWaterChaosCarrierWitness.mummuTiamatuOriginCarrier ∧
    tiamatLifeStrengthCarrier tiamatStrengthTransmission := by
  exact ⟨MummuTiamatuWaterChaosCarrierWitness.mummu_tiamatu_carries_origin,
    cutha_tiamat_life_strength_carrier⟩

theorem cutha_monster_boundary_bridge :
    Gnosis.GreekMonsterErrorPrimitivesWitness.monsterBoundaryMarkers
      Gnosis.GreekMonsterErrorPrimitivesWitness.greekMonsterAtlas ∧
    turbidCompositeCreatureLayer cuthaWaterCreatureLayer := by
  exact ⟨Gnosis.GreekMonsterErrorPrimitivesWitness.monsters_mark_namespace_logic_gates,
    cutha_turbid_composite_creature_layer⟩

theorem cutha_composite_creature_witness :
    variantCosmogonyBranch variantTraditionBranch ∧
    turbidCompositeCreatureLayer cuthaWaterCreatureLayer ∧
    tiamatLifeStrengthCarrier tiamatStrengthTransmission ∧
    cuthaDestructionLedger destructionAndFutureKingLedger ∧
    sevenSpiritBoundaryWitness sevenSpiritStormBoundary := by
  exact ⟨cutha_variant_cosmogony_branch,
    cutha_turbid_composite_creature_layer,
    cutha_tiamat_life_strength_carrier,
    cutha_destruction_ledger,
    cutha_seven_spirit_boundary⟩

end CuthaCompositeCreatureWitness
end Gnosis.Witnesses.Chaldean
