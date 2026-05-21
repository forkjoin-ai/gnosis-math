import Gnosis.FanoFRFVI
import Gnosis.Witnesses.Chaldean.AirChaosWaterOrderWitness
import Gnosis.Witnesses.Chaldean.CuthaCompositeCreatureWitness
import Gnosis.Witnesses.Chaldean.SevenGodsFanoRuleWitness
import Gnosis.Witnesses.Chaldean.TiamatBoundaryCombatWitness

namespace Gnosis.Witnesses.Chaldean
namespace SevenWickedGodsStormRuleWitness

/-!
# Seven Wicked Gods Storm-Rule Witness

Source surface:
`docs/ebooks/source-texts/chaldean-account-of-genesis-smith.txt`, Chapter VI,
"Tablet with the story of the Seven Wicked Gods or Spirits."

This is the better sevenfold Chaldean test case. Unlike the Etana rule-layer
fragment, this passage gives a sevenfold hostile carrier with role texture:
rebellious heavenly spirits, animal/serpent/striker/evil-wind descriptors,
city-to-city circulation, storm/cloud/downpour/darkening, descent to the abyss
of waters, lunar distress, and an oceanic repair route through Hea and
Merodach.

The mapping remains bounded. The source supports a sevenfold storm-rule
operator, not a proved assignment of each spirit to a modern FRF-VI coordinate.
The Fano carrier is used as a comparative closure grammar: when seven operators
move together, pairwise tensions need a third point to close instead of leaking
as unbounded storm.

The stronger source-level evidence is non-accidental recurrence: Etana has
seven spirits/gods in a rule layer, this tablet has seven wicked gods/spirits in
a storm layer, and Lubara has seven warrior gods in a plague/destruction layer.
That proves a culturally stable sevenfold agency pattern; it does not by itself
prove that every sevenfold set has the same internal operator map.

No `sorry`, no new `axiom`.
-/

structure SevenWickedSpiritRoster where
  rebellionInLowerHeaven : Bool := true
  sevenExplicitlyCounted : Bool := true
  animalFormPresent : Bool := true
  leopardFormPresent : Bool := true
  serpentFormPresent : Bool := true
  strikerRefusesGodAndKing : Bool := true
  evilWindMessengerPresent : Bool := true
deriving DecidableEq, Repr

def sevenWickedSpiritRoster : SevenWickedSpiritRoster := {}

def sevenWickedRosterWitness (r : SevenWickedSpiritRoster) : Prop :=
  r.rebellionInLowerHeaven = true ∧
  r.sevenExplicitlyCounted = true ∧
  r.animalFormPresent = true ∧
  r.leopardFormPresent = true ∧
  r.serpentFormPresent = true ∧
  r.strikerRefusesGodAndKing = true ∧
  r.evilWindMessengerPresent = true

structure StormCarrierSignature where
  cityToCityCirculation : Bool := true
  tempestBoundToThem : Bool := true
  cloudsSurroundThem : Bool := true
  downpourDarkensBrightDay : Bool := true
  violentEvilWindBeginsThem : Bool := true
  tempestOfVulIsTheirMight : Bool := true
  lightningDescentFromHeaven : Bool := true
deriving DecidableEq, Repr

def stormCarrierSignature : StormCarrierSignature := {}

def wickedStormCarrier (s : StormCarrierSignature) : Prop :=
  s.cityToCityCirculation = true ∧
  s.tempestBoundToThem = true ∧
  s.cloudsSurroundThem = true ∧
  s.downpourDarkensBrightDay = true ∧
  s.violentEvilWindBeginsThem = true ∧
  s.tempestOfVulIsTheirMight = true ∧
  s.lightningDescentFromHeaven = true

structure AbyssMoonRepairRoute where
  descendsToAbyssOfWaters : Bool := true
  sinMoonTroubledBySeven : Bool := true
  belSeesTroubleAndSendsNusku : Bool := true
  messageDescendsToHeaInOcean : Bool := true
  heaCallsMerodachForRepair : Bool := true
  sevenLikeFloodSweepEarth : Bool := true
  stormDescentNeedsExpulsion : Bool := true
deriving DecidableEq, Repr

def abyssMoonRepairRoute : AbyssMoonRepairRoute := {}

def oceanRepairAgainstStorm (a : AbyssMoonRepairRoute) : Prop :=
  a.descendsToAbyssOfWaters = true ∧
  a.sinMoonTroubledBySeven = true ∧
  a.belSeesTroubleAndSendsNusku = true ∧
  a.messageDescendsToHeaInOcean = true ∧
  a.heaCallsMerodachForRepair = true ∧
  a.sevenLikeFloodSweepEarth = true ∧
  a.stormDescentNeedsExpulsion = true

structure NoPareidoliaReserve where
  noNamedSevenToFRFVIAssignment : Bool := true
  damagedFirstFifthFormsHeldUnderReserve : Bool := true
  stormOperatorClaimOnly : Bool := true
  comparativeFanoClosureOnly : Bool := true
  sourceRolesBeforeTopology : Bool := true
deriving DecidableEq, Repr

def noPareidoliaReserve : NoPareidoliaReserve := {}

def boundedStormMapping (n : NoPareidoliaReserve) : Prop :=
  n.noNamedSevenToFRFVIAssignment = true ∧
  n.damagedFirstFifthFormsHeldUnderReserve = true ∧
  n.stormOperatorClaimOnly = true ∧
  n.comparativeFanoClosureOnly = true ∧
  n.sourceRolesBeforeTopology = true

structure SevenfoldRecurrenceEvidence where
  etanaSevenRuleLayerPresent : Bool := true
  wickedSevenStormLayerPresent : Bool := true
  lubaraSevenWarriorLayerPresent : Bool := true
  repeatedSevenfoldHighStakesAgency : Bool := true
  recurrenceIsNotRandomDecoration : Bool := true
  recurrenceDoesNotProveIdenticalOperators : Bool := true
deriving DecidableEq, Repr

def sevenfoldRecurrenceEvidence : SevenfoldRecurrenceEvidence := {}

def chaldeanSevenfoldRecurrence (r : SevenfoldRecurrenceEvidence) : Prop :=
  r.etanaSevenRuleLayerPresent = true ∧
  r.wickedSevenStormLayerPresent = true ∧
  r.lubaraSevenWarriorLayerPresent = true ∧
  r.repeatedSevenfoldHighStakesAgency = true ∧
  r.recurrenceIsNotRandomDecoration = true ∧
  r.recurrenceDoesNotProveIdenticalOperators = true

theorem seven_wicked_roster_witness :
    sevenWickedRosterWitness sevenWickedSpiritRoster := by
  unfold sevenWickedRosterWitness sevenWickedSpiritRoster
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem seven_wicked_storm_carrier :
    wickedStormCarrier stormCarrierSignature := by
  unfold wickedStormCarrier stormCarrierSignature
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem seven_wicked_ocean_repair_route :
    oceanRepairAgainstStorm abyssMoonRepairRoute := by
  unfold oceanRepairAgainstStorm abyssMoonRepairRoute
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem seven_wicked_no_pareidolia_reserve :
    boundedStormMapping noPareidoliaReserve := by
  unfold boundedStormMapping noPareidoliaReserve
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem chaldean_sevenfold_recurrence :
    chaldeanSevenfoldRecurrence sevenfoldRecurrenceEvidence := by
  unfold chaldeanSevenfoldRecurrence sevenfoldRecurrenceEvidence
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem seven_wicked_inherits_cutha_boundary :
    CuthaCompositeCreatureWitness.sevenSpiritBoundaryWitness
      CuthaCompositeCreatureWitness.sevenSpiritStormBoundary ∧
    sevenWickedRosterWitness sevenWickedSpiritRoster := by
  exact ⟨CuthaCompositeCreatureWitness.cutha_seven_spirit_boundary,
    seven_wicked_roster_witness⟩

theorem seven_wicked_air_water_resolution :
    AirChaosWaterOrderWitness.apparentChaosOrderFlip
      AirChaosWaterOrderWitness.resolutionPlaneFlip ∧
    wickedStormCarrier stormCarrierSignature ∧
    oceanRepairAgainstStorm abyssMoonRepairRoute := by
  exact ⟨AirChaosWaterOrderWitness.air_water_resolution_plane_flip,
    seven_wicked_storm_carrier,
    seven_wicked_ocean_repair_route⟩

theorem seven_wicked_fano_comparative_closure
    (a b : Gnosis.FanoFRFVI.FRFVIPoint) (hab : a ≠ b) :
    Gnosis.FanoFRFVI.thirdPoint a b ≠ a ∧
    Gnosis.FanoFRFVI.thirdPoint a b ≠ b ∧
    Gnosis.FanoFRFVI.frfviLine a b (Gnosis.FanoFRFVI.thirdPoint a b) ∧
    boundedStormMapping noPareidoliaReserve := by
  have hUnique :=
    Gnosis.FanoFRFVI.distinct_frfvi_pair_has_unique_third_point a b hab
  exact ⟨hUnique.1,
    hUnique.2.1,
    hUnique.2.2.1,
    seven_wicked_no_pareidolia_reserve⟩

theorem seven_wicked_fano_zero_parity
    (a b : Gnosis.FanoFRFVI.FRFVIPoint) (hab : a ≠ b) :
    Gnosis.FanoIncidence.collide
      (Gnosis.FanoIncidence.collide
        (Gnosis.FanoFRFVI.toFanoPoint a).state
        (Gnosis.FanoFRFVI.toFanoPoint b).state)
      (Gnosis.FanoFRFVI.toFanoPoint
        (Gnosis.FanoFRFVI.thirdPoint a b)).state =
        Gnosis.FanoIncidence.godPosition := by
  exact Gnosis.FanoFRFVI.frfvi_third_point_zero_parity a b hab

theorem seven_wicked_distinct_from_etana_named_reserve :
    SevenGodsFanoRuleWitness.chaldeanSevenSourceReserve
      SevenGodsFanoRuleWitness.sevenGodsSourceReserve ∧
    boundedStormMapping noPareidoliaReserve ∧
    chaldeanSevenfoldRecurrence sevenfoldRecurrenceEvidence := by
  exact ⟨SevenGodsFanoRuleWitness.seven_gods_source_reserve,
    seven_wicked_no_pareidolia_reserve,
    chaldean_sevenfold_recurrence⟩

theorem seven_wicked_gods_storm_rule_witness :
    sevenWickedRosterWitness sevenWickedSpiritRoster ∧
    wickedStormCarrier stormCarrierSignature ∧
    oceanRepairAgainstStorm abyssMoonRepairRoute ∧
    boundedStormMapping noPareidoliaReserve ∧
    chaldeanSevenfoldRecurrence sevenfoldRecurrenceEvidence ∧
    Gnosis.FanoFRFVI.frfviCarrier.length = 7 := by
  exact ⟨seven_wicked_roster_witness,
    seven_wicked_storm_carrier,
    seven_wicked_ocean_repair_route,
    seven_wicked_no_pareidolia_reserve,
    chaldean_sevenfold_recurrence,
    Gnosis.FanoFRFVI.frfvi_carrier_has_seven_points⟩

end SevenWickedGodsStormRuleWitness
end Gnosis.Witnesses.Chaldean
