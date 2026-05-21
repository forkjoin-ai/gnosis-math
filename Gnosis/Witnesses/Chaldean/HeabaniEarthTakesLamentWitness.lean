import Gnosis.Witnesses.Chaldean.HumbabaForestGateTempestWitness
import Gnosis.Witnesses.Chaldean.IzdubarErechReturnCityBoundaryWitness

namespace Gnosis.Witnesses.Chaldean
namespace HeabaniEarthTakesLamentWitness

/-!
# Heabani Earth-Takes Lament Witness

Source surface:
`docs/ebooks/source-texts/chaldean-account-of-genesis-smith.txt`, Chapter XII
ending / twelfth tablet fragments of the Izdubar legends.

The lament is a negative affordance ledger. Death is named by interfaces lost:
no banquet, no assembly call, no bow lifting, no mace grasping, no shoes, no
slain enemy stretched out, no kissing or striking wife/child. Then the source
narrows the death-agent: Simtar did not take him, Asakku did not take him,
Nergal's resting place did not take him, battle did not strike him; earth took
him. Merodach later opens the earth and the spirit of Heabani rises like glass,
but the returned witness refuses immediate disclosure.

No `sorry`, no new `axiom`.
-/

structure LostAffordanceLedger where
  banquetNotShared : Bool := true
  assemblyCallLost : Bool := true
  bowNotLifted : Bool := true
  maceNotGrasped : Bool := true
  shoesNotWorn : Bool := true
  familyContactLost : Bool := true
deriving DecidableEq, Repr

def lostAffordanceLedger : LostAffordanceLedger := {}

def deathRemovesAffordances (l : LostAffordanceLedger) : Prop :=
  l.banquetNotShared = true ∧
  l.assemblyCallLost = true ∧
  l.bowNotLifted = true ∧
  l.maceNotGrasped = true ∧
  l.shoesNotWorn = true ∧
  l.familyContactLost = true

structure EarthTakesExclusion where
  armsOfEarthTakeHim : Bool := true
  simtarDidNotTakeHim : Bool := true
  asakkuDidNotTakeHim : Bool := true
  nergalRestingPlaceDidNotTakeHim : Bool := true
  battleHeroesDidNotStrikeHim : Bool := true
  earthTakesRepeated : Bool := true
deriving DecidableEq, Repr

def earthTakesExclusion : EarthTakesExclusion := {}

def earthTakesByExclusion (e : EarthTakesExclusion) : Prop :=
  e.armsOfEarthTakeHim = true ∧
  e.simtarDidNotTakeHim = true ∧
  e.asakkuDidNotTakeHim = true ∧
  e.nergalRestingPlaceDidNotTakeHim = true ∧
  e.battleHeroesDidNotStrikeHim = true ∧
  e.earthTakesRepeated = true

structure DarknessMantleEnclosure where
  darknessMotherNinazuNamed : Bool := true
  mantleCoversBody : Bool := true
  feetEnclosedLikeDeepWell : Bool := true
  earthMightTakesHim : Bool := true
  woundToEarthStrikesIzdubar : Bool := true
deriving DecidableEq, Repr

def darknessMantleEnclosure : DarknessMantleEnclosure := {}

def earthEnclosesBodyState (d : DarknessMantleEnclosure) : Prop :=
  d.darknessMotherNinazuNamed = true ∧
  d.mantleCoversBody = true ∧
  d.feetEnclosedLikeDeepWell = true ∧
  d.earthMightTakesHim = true ∧
  d.woundToEarthStrikesIzdubar = true

structure TransparentGhostDisclosure where
  merodachOpensEarth : Bool := true
  heabaniSpiritRises : Bool := true
  spiritLikeGlass : Bool := true
  visionCalledTerrible : Bool := true
  disclosureDelayedUntilEarthCovers : Bool := true
deriving DecidableEq, Repr

def transparentGhostDisclosure : TransparentGhostDisclosure := {}

def ghostWitnessUnderDelay (g : TransparentGhostDisclosure) : Prop :=
  g.merodachOpensEarth = true ∧
  g.heabaniSpiritRises = true ∧
  g.spiritLikeGlass = true ∧
  g.visionCalledTerrible = true ∧
  g.disclosureDelayedUntilEarthCovers = true

theorem heabani_death_removes_affordances :
    deathRemovesAffordances lostAffordanceLedger := by
  unfold deathRemovesAffordances lostAffordanceLedger
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem heabani_earth_takes_by_exclusion :
    earthTakesByExclusion earthTakesExclusion := by
  unfold earthTakesByExclusion earthTakesExclusion
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem heabani_earth_encloses_body_state :
    earthEnclosesBodyState darknessMantleEnclosure := by
  unfold earthEnclosesBodyState darknessMantleEnclosure
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem heabani_ghost_witness_under_delay :
    ghostWitnessUnderDelay transparentGhostDisclosure := by
  unfold ghostWitnessUnderDelay transparentGhostDisclosure
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem heabani_contrasts_erech_reintegration :
    IzdubarErechReturnCityBoundaryWitness.erechBoundaryMeasured
      IzdubarErechReturnCityBoundaryWitness.cityBoundarySurvey ∧
    deathRemovesAffordances lostAffordanceLedger := by
  exact ⟨IzdubarErechReturnCityBoundaryWitness.izdubar_erech_boundary_measured,
    heabani_death_removes_affordances⟩

theorem heabani_inherits_humbaba_battle_context :
    HumbabaForestGateTempestWitness.expeditionRiskWitness
      HumbabaForestGateTempestWitness.unknownExpeditionRisk ∧
    earthTakesByExclusion earthTakesExclusion := by
  exact ⟨HumbabaForestGateTempestWitness.humbaba_expedition_risk,
    heabani_earth_takes_by_exclusion⟩

theorem heabani_earth_takes_lament_witness :
    deathRemovesAffordances lostAffordanceLedger ∧
    earthTakesByExclusion earthTakesExclusion ∧
    earthEnclosesBodyState darknessMantleEnclosure ∧
    ghostWitnessUnderDelay transparentGhostDisclosure := by
  exact ⟨heabani_death_removes_affordances,
    heabani_earth_takes_by_exclusion,
    heabani_earth_encloses_body_state,
    heabani_ghost_witness_under_delay⟩

end HeabaniEarthTakesLamentWitness
end Gnosis.Witnesses.Chaldean
