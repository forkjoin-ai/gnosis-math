import Gnosis.Witnesses.Folklore.ZodiacTwelvefoldOperatorSystemWitness

namespace Gnosis.Witnesses.Folklore
namespace AriesInitiationSparkWitness

/-!
# Aries Initiation Spark Witness

Aries upgrades the first zodiac scaffold operator from assignment to bounded
mythic shape.

The Aries carrier is the ram at the beginning of the cycle: a force that moves
first, breaks ground, and carries vulnerable agents across a lethal boundary.
In the Greek golden-ram / Golden Fleece complex, the ram is not decorative. It
initiates escape, crosses air/sea danger, leaves behind a fleece that becomes a
quest target, and turns raw rescue into a downstream heroic mission. In zodiac
cycle language, Aries also marks the spring/equinox threshold: the wheel's
ignition point, not its settled harvest.

This witness therefore treats Aries as initiation spark under reserve: first
impulse, competitive breach of inertia, rescue-launch, and quest-seed export.
It does not claim all Aries symbolism has been source-exhausted.

No `sorry`, no new `axiom`.
-/

structure RamInitiationCarrier where
  ramMovesFirst : Bool := true
  rawImpulseBreaksInertia : Bool := true
  vulnerableAgentsCarried : Bool := true
  lethalBoundaryCrossed : Bool := true
  rescuePrecedesInstitution : Bool := true
deriving DecidableEq, Repr

def ramInitiationCarrier : RamInitiationCarrier := {}

def ramCarriesInitiationSpark
    (r : RamInitiationCarrier) : Prop :=
  r.ramMovesFirst = true ∧
  r.rawImpulseBreaksInertia = true ∧
  r.vulnerableAgentsCarried = true ∧
  r.lethalBoundaryCrossed = true ∧
  r.rescuePrecedesInstitution = true

structure GoldenFleeceQuestSeed where
  fleeceRemainsAfterRamTransit : Bool := true
  rescueLeavesDurableToken : Bool := true
  tokenBecomesQuestTarget : Bool := true
  downstreamHeroicMissionSeeded : Bool := true
  initiationExportsFutureWork : Bool := true
deriving DecidableEq, Repr

def goldenFleeceQuestSeed : GoldenFleeceQuestSeed := {}

def fleeceConvertsEscapeIntoQuestSeed
    (g : GoldenFleeceQuestSeed) : Prop :=
  g.fleeceRemainsAfterRamTransit = true ∧
  g.rescueLeavesDurableToken = true ∧
  g.tokenBecomesQuestTarget = true ∧
  g.downstreamHeroicMissionSeeded = true ∧
  g.initiationExportsFutureWork = true

structure SpringEquinoxCycleIgnition where
  firstSignOfCycle : Bool := true
  springThresholdNamed : Bool := true
  lightGrowthAfterEquilibrium : Bool := true
  ignitionNotHarvest : Bool := true
  cycleStartsByCrossing : Bool := true
deriving DecidableEq, Repr

def springEquinoxCycleIgnition : SpringEquinoxCycleIgnition := {}

def ariesMarksCycleIgnition
    (s : SpringEquinoxCycleIgnition) : Prop :=
  s.firstSignOfCycle = true ∧
  s.springThresholdNamed = true ∧
  s.lightGrowthAfterEquilibrium = true ∧
  s.ignitionNotHarvest = true ∧
  s.cycleStartsByCrossing = true

structure AriesOperatorUpgrade where
  zodiacOperatorIsInitiationSpark : Bool := true
  scaffoldUpgradedByRamCarrier : Bool := true
  competitiveDriveBreaksGround : Bool := true
  sourceReserveStillHeld : Bool := true
  notReducedToPersonalityStereotype : Bool := true
deriving DecidableEq, Repr

def ariesOperatorUpgrade : AriesOperatorUpgrade := {}

def ariesUpgradesInitiationOperator
    (a : AriesOperatorUpgrade) : Prop :=
  a.zodiacOperatorIsInitiationSpark = true ∧
  a.scaffoldUpgradedByRamCarrier = true ∧
  a.competitiveDriveBreaksGround = true ∧
  a.sourceReserveStillHeld = true ∧
  a.notReducedToPersonalityStereotype = true

theorem aries_ram_carries_initiation_spark :
    ramCarriesInitiationSpark ramInitiationCarrier := by
  unfold ramCarriesInitiationSpark ramInitiationCarrier
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem aries_fleece_converts_escape_into_quest_seed :
    fleeceConvertsEscapeIntoQuestSeed goldenFleeceQuestSeed := by
  unfold fleeceConvertsEscapeIntoQuestSeed goldenFleeceQuestSeed
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem aries_marks_cycle_ignition :
    ariesMarksCycleIgnition springEquinoxCycleIgnition := by
  unfold ariesMarksCycleIgnition springEquinoxCycleIgnition
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem aries_upgrades_initiation_operator :
    ariesUpgradesInitiationOperator ariesOperatorUpgrade := by
  unfold ariesUpgradesInitiationOperator ariesOperatorUpgrade
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem aries_imports_twelvefold_operator_anchor :
    ZodiacTwelvefoldOperatorSystemWitness.signOperator
      ZodiacTwelvefoldOperatorSystemWitness.ZodiacSign.aries =
        ZodiacTwelvefoldOperatorSystemWitness.ZodiacOperator.initiationSpark ∧
    ZodiacTwelvefoldOperatorSystemWitness.twelvefoldZodiacCanIndexGnosisTimeWaves
      ZodiacTwelvefoldOperatorSystemWitness.gnosisTimeWaveReserve ∧
    ariesUpgradesInitiationOperator ariesOperatorUpgrade := by
  exact ⟨ZodiacTwelvefoldOperatorSystemWitness.zodiac_operator_assignments_anchor.1,
    ZodiacTwelvefoldOperatorSystemWitness.zodiac_twelvefold_can_index_gnosis_time_waves,
    aries_upgrades_initiation_operator⟩

theorem aries_initiation_spark_witness :
    ramCarriesInitiationSpark ramInitiationCarrier ∧
    fleeceConvertsEscapeIntoQuestSeed goldenFleeceQuestSeed ∧
    ariesMarksCycleIgnition springEquinoxCycleIgnition ∧
    ariesUpgradesInitiationOperator ariesOperatorUpgrade := by
  exact ⟨aries_ram_carries_initiation_spark,
    aries_fleece_converts_escape_into_quest_seed,
    aries_marks_cycle_ignition,
    aries_upgrades_initiation_operator⟩

theorem aries_establishes_scaffold_origin :
    ZodiacTwelvefoldOperatorSystemWitness.isOriginIndex 0 ∧
    ariesMarksCycleIgnition springEquinoxCycleIgnition ∧
    ariesUpgradesInitiationOperator ariesOperatorUpgrade := by
  exact ⟨ZodiacTwelvefoldOperatorSystemWitness.zero_is_origin_index,
    aries_marks_cycle_ignition,
    aries_upgrades_initiation_operator⟩

end AriesInitiationSparkWitness
end Gnosis.Witnesses.Folklore
