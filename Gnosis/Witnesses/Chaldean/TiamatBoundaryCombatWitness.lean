import Gnosis.Witnesses.Chaldean.MummuTiamatuWaterChaosCarrierWitness

namespace Gnosis.Witnesses.Chaldean
namespace TiamatBoundaryCombatWitness

/-!
# Tiamat Boundary Combat Witness

Source surface:
`docs/ebooks/source-texts/chaldean-account-of-genesis-smith.txt`, Chapter V,
war fragments after the fall/curse material.

The source keeps insisting on reserve: speeches are broken, order is uncertain,
and the fragments cannot be flattened into a single clean sequence. Still, the
combat topology is clear. The dragon of the sea is linked to Tiamat, the living
principle of sea-chaos; the powers of evil are led by Tiamat; weapons are
fabricated for the god who will meet the dragon; sword, bow, lightning,
thunderbolt, winds, and fetters become boundary tools; and Tiamat's open mouth
is defeated by wind entering before it can close.

The witness is not "order deletes chaos." It is sea-taming under adversarial
pressure. The same water-chaos that carries origin also trains the operator:
friend as substrate, foe as flood/dragon, strength through bounded combat.

No `sorry`, no new `axiom`.
-/

structure FragmentaryCombatReserve where
  speechesBroken : Bool := true
  orderUncertain : Bool := true
  tooMutilatedForSingleSequence : Bool := true
  directProofOfTimingWithheld : Bool := true
  commentReservedUntilTextComplete : Bool := true
deriving DecidableEq, Repr

def fragmentaryCombatReserve : FragmentaryCombatReserve := {}

def combatReserveDiscipline (r : FragmentaryCombatReserve) : Prop :=
  r.speechesBroken = true ∧
  r.orderUncertain = true ∧
  r.tooMutilatedForSingleSequence = true ∧
  r.directProofOfTimingWithheld = true ∧
  r.commentReservedUntilTextComplete = true

structure SeaDragonBoundary where
  dragonCreatureOfTiamat : Bool := true
  seaChaosOpposesOrderedDeities : Bool := true
  dragonLinkedToFallCurse : Bool := true
  powersOfEvilLedByTiamat : Bool := true
  tiamatDistinguishedFromSeaMonsterUnderReserve : Bool := true
deriving DecidableEq, Repr

def seaDragonBoundary : SeaDragonBoundary := {}

def tiamatDragonBoundary (b : SeaDragonBoundary) : Prop :=
  b.dragonCreatureOfTiamat = true ∧
  b.seaChaosOpposesOrderedDeities = true ∧
  b.dragonLinkedToFallCurse = true ∧
  b.powersOfEvilLedByTiamat = true ∧
  b.tiamatDistinguishedFromSeaMonsterUnderReserve = true

structure BoundaryWeaponKit where
  swordMadeAndSeenByGods : Bool := true
  bowStrungAndHonored : Bool := true
  lightningSentBeforeCombatant : Bool := true
  thunderboltCarriedAsGreatWeapon : Bool := true
  fettersFastenSeaDragonHands : Bool := true
deriving DecidableEq, Repr

def boundaryWeaponKit : BoundaryWeaponKit := {}

def combatBoundaryTools (w : BoundaryWeaponKit) : Prop :=
  w.swordMadeAndSeenByGods = true ∧
  w.bowStrungAndHonored = true ∧
  w.lightningSentBeforeCombatant = true ∧
  w.thunderboltCarriedAsGreatWeapon = true ∧
  w.fettersFastenSeaDragonHands = true

structure WindMouthContainment where
  sevenWindsFixed : Bool := true
  evilHostileTempestStormNamed : Bool := true
  windsBroughtOutAsCreatedTools : Bool := true
  tiamatOpensMouthToSwallow : Bool := true
  windEntersBeforeClosureAndBreaksHeart : Bool := true
deriving DecidableEq, Repr

def windMouthContainment : WindMouthContainment := {}

def windContainmentProtocol (w : WindMouthContainment) : Prop :=
  w.sevenWindsFixed = true ∧
  w.evilHostileTempestStormNamed = true ∧
  w.windsBroughtOutAsCreatedTools = true ∧
  w.tiamatOpensMouthToSwallow = true ∧
  w.windEntersBeforeClosureAndBreaksHeart = true

structure SeaTamingTrainingLoad where
  originCarrierAlsoAdversary : Bool := true
  combatOccursAtBoundary : Bool := true
  containmentProducesOperatorStrength : Bool := true
  alliesScatterAfterLeaderFalls : Bool := true
  boundedChaosImprovesWorldStability : Bool := true
deriving DecidableEq, Repr

def seaTamingTrainingLoad : SeaTamingTrainingLoad := {}

def tiamatTrainingLoad (t : SeaTamingTrainingLoad) : Prop :=
  t.originCarrierAlsoAdversary = true ∧
  t.combatOccursAtBoundary = true ∧
  t.containmentProducesOperatorStrength = true ∧
  t.alliesScatterAfterLeaderFalls = true ∧
  t.boundedChaosImprovesWorldStability = true

theorem tiamat_combat_reserve_discipline :
    combatReserveDiscipline fragmentaryCombatReserve := by
  unfold combatReserveDiscipline fragmentaryCombatReserve
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem tiamat_dragon_boundary_witness :
    tiamatDragonBoundary seaDragonBoundary := by
  unfold tiamatDragonBoundary seaDragonBoundary
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem tiamat_combat_boundary_tools :
    combatBoundaryTools boundaryWeaponKit := by
  unfold combatBoundaryTools boundaryWeaponKit
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem tiamat_wind_containment_protocol :
    windContainmentProtocol windMouthContainment := by
  unfold windContainmentProtocol windMouthContainment
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem tiamat_training_load_witness :
    tiamatTrainingLoad seaTamingTrainingLoad := by
  unfold tiamatTrainingLoad seaTamingTrainingLoad
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem tiamat_inherits_mummu_tiamatu_friend_foe :
    MummuTiamatuWaterChaosCarrierWitness.seaFriendFoeTaming
      MummuTiamatuWaterChaosCarrierWitness.seaTamingAmbivalence ∧
    tiamatTrainingLoad seaTamingTrainingLoad := by
  exact ⟨MummuTiamatuWaterChaosCarrierWitness.mummu_tiamatu_sea_friend_foe_taming,
    tiamat_training_load_witness⟩

theorem tiamat_boundary_combat_witness :
    combatReserveDiscipline fragmentaryCombatReserve ∧
    tiamatDragonBoundary seaDragonBoundary ∧
    combatBoundaryTools boundaryWeaponKit ∧
    windContainmentProtocol windMouthContainment ∧
    tiamatTrainingLoad seaTamingTrainingLoad := by
  exact ⟨tiamat_combat_reserve_discipline,
    tiamat_dragon_boundary_witness,
    tiamat_combat_boundary_tools,
    tiamat_wind_containment_protocol,
    tiamat_training_load_witness⟩

end TiamatBoundaryCombatWitness
end Gnosis.Witnesses.Chaldean
