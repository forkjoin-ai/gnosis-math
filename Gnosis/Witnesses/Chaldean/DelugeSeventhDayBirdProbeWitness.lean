import Gnosis.Witnesses.Chaldean.AirChaosWaterOrderWitness
import Gnosis.Witnesses.Chaldean.SevenfoldAgencyRecurrenceMetaWitness

namespace Gnosis.Witnesses.Chaldean
namespace DelugeSeventhDayBirdProbeWitness

/-!
# Deluge Seventh-Day Bird-Probe Witness

Source surface:
`docs/ebooks/source-texts/chaldean-account-of-genesis-smith.txt`, Chapter XII,
Chaldean deluge account.

The deluge passage is a state-preservation protocol. The ship is closed; grain,
goods, wealth, servants, people, beasts, and the "seed of life" are loaded into
the sealed carrier. Wind, deluge, and storm overwhelm for six days and nights;
on the seventh day the storm and deluge calm, sea dries, and wind/deluge end.
The survivor then samples the world by staged bird probes: dove returns without
rest, swallow returns without rest, raven observes water decrease and does not
return. Afterward animals are sent to the four winds and altar herbs are cut by
sevens.

The topology is not only punishment. It is closure, sampling, release, and
re-synchronization after overload.

No `sorry`, no new `axiom`.
-/

structure SealedShipCarrier where
  doorTurnedClosed : Bool := true
  grainGoodsWealthLoaded : Bool := true
  servantsPeopleAnimalsLoaded : Bool := true
  seedOfLifeLoaded : Bool := true
  bitumenSealsInsideAndOutside : Bool := true
deriving DecidableEq, Repr

def sealedShipCarrier : SealedShipCarrier := {}

def shipPreservesState (s : SealedShipCarrier) : Prop :=
  s.doorTurnedClosed = true ∧
  s.grainGoodsWealthLoaded = true ∧
  s.servantsPeopleAnimalsLoaded = true ∧
  s.seedOfLifeLoaded = true ∧
  s.bitumenSealsInsideAndOutside = true

structure SeventhDayResolution where
  sixDaysNightsOverwhelmed : Bool := true
  windDelugeStormNamed : Bool := true
  seventhDayStormCalmed : Bool := true
  seaDried : Bool := true
  windAndDelugeEnded : Bool := true
deriving DecidableEq, Repr

def seventhDayResolution : SeventhDayResolution := {}

def seventhDayEndsOverload (r : SeventhDayResolution) : Prop :=
  r.sixDaysNightsOverwhelmed = true ∧
  r.windDelugeStormNamed = true ∧
  r.seventhDayStormCalmed = true ∧
  r.seaDried = true ∧
  r.windAndDelugeEnded = true

structure BirdProbeSequence where
  windowOpenedLightBreaksIn : Bool := true
  doveReturnsNoRestingPlace : Bool := true
  swallowReturnsNoRestingPlace : Bool := true
  ravenSeesWaterDecrease : Bool := true
  ravenDoesNotReturn : Bool := true
deriving DecidableEq, Repr

def birdProbeSequence : BirdProbeSequence := {}

def birdsSampleWorldState (b : BirdProbeSequence) : Prop :=
  b.windowOpenedLightBreaksIn = true ∧
  b.doveReturnsNoRestingPlace = true ∧
  b.swallowReturnsNoRestingPlace = true ∧
  b.ravenSeesWaterDecrease = true ∧
  b.ravenDoesNotReturn = true

structure PostFloodResynchronization where
  animalsSentToFourWinds : Bool := true
  libationPoured : Bool := true
  altarBuiltOnMountainPeak : Bool := true
  herbsCutBySevens : Bool := true
  godsGatherAtSavour : Bool := true
deriving DecidableEq, Repr

def postFloodResynchronization : PostFloodResynchronization := {}

def altarResynchronizesWorld (p : PostFloodResynchronization) : Prop :=
  p.animalsSentToFourWinds = true ∧
  p.libationPoured = true ∧
  p.altarBuiltOnMountainPeak = true ∧
  p.herbsCutBySevens = true ∧
  p.godsGatherAtSavour = true

theorem deluge_ship_preserves_state :
    shipPreservesState sealedShipCarrier := by
  unfold shipPreservesState sealedShipCarrier
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem deluge_seventh_day_ends_overload :
    seventhDayEndsOverload seventhDayResolution := by
  unfold seventhDayEndsOverload seventhDayResolution
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem deluge_birds_sample_world_state :
    birdsSampleWorldState birdProbeSequence := by
  unfold birdsSampleWorldState birdProbeSequence
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem deluge_altar_resynchronizes_world :
    altarResynchronizesWorld postFloodResynchronization := by
  unfold altarResynchronizesWorld postFloodResynchronization
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem deluge_inherits_air_water_resolution :
    AirChaosWaterOrderWitness.separatesWaterOrderFromAirChaos
      AirChaosWaterOrderWitness.waterAirSeparation ∧
    seventhDayEndsOverload seventhDayResolution := by
  exact ⟨AirChaosWaterOrderWitness.water_air_role_separation,
    deluge_seventh_day_ends_overload⟩

theorem deluge_inherits_sevenfold_recurrence :
    SevenfoldAgencyRecurrenceMetaWitness.sevenfoldActsAsStableCardinality
      SevenfoldAgencyRecurrenceMetaWitness.sevenfoldTopologyReading ∧
    altarResynchronizesWorld postFloodResynchronization := by
  exact ⟨SevenfoldAgencyRecurrenceMetaWitness.sevenfold_stable_cardinality,
    deluge_altar_resynchronizes_world⟩

theorem deluge_seventh_day_bird_probe_witness :
    shipPreservesState sealedShipCarrier ∧
    seventhDayEndsOverload seventhDayResolution ∧
    birdsSampleWorldState birdProbeSequence ∧
    altarResynchronizesWorld postFloodResynchronization := by
  exact ⟨deluge_ship_preserves_state,
    deluge_seventh_day_ends_overload,
    deluge_birds_sample_world_state,
    deluge_altar_resynchronizes_world⟩

end DelugeSeventhDayBirdProbeWitness
end Gnosis.Witnesses.Chaldean
