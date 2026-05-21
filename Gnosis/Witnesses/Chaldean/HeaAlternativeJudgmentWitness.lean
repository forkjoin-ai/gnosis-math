import Gnosis.Witnesses.Chaldean.DelugeSeventhDayBirdProbeWitness
import Gnosis.Witnesses.Chaldean.LubaraSevenWarriorGodsWitness
import Gnosis.Witnesses.Chaldean.MummuTiamatuWaterChaosCarrierWitness

namespace Gnosis.Witnesses.Chaldean
namespace HeaAlternativeJudgmentWitness

/-!
# Hea Alternative Judgment Witness

Source surface:
`docs/ebooks/source-texts/chaldean-account-of-genesis-smith.txt`, Chapter XII,
post-deluge exchange between Hea and Bel/Elu.

This is the deluge counterproof. Hea does not deny evil; he rejects
indiscriminate global reset. The doer of sin did his sin, and the doer of evil
did his evil, but the just prince should not be cut off and the faithful should
not be destroyed. Instead of a deluge, Hea proposes bounded correction operators:
lions, leopards, famine, and pestilence.

The topology is judgment with locality. Global flood erases too much state;
bounded correction preserves responsibility gradients and survivor integrity.

No `sorry`, no new `axiom`.
-/

structure DelugeOverreach where
  angerMakesDeluge : Bool := true
  noOneAllowedOutAlive : Bool := true
  savedManRejectedFromDeep : Bool := true
  justWouldBeCutOff : Bool := true
  faithfulWouldBeDestroyed : Bool := true
deriving DecidableEq, Repr

def delugeOverreach : DelugeOverreach := {}

def globalResetOverreaches (d : DelugeOverreach) : Prop :=
  d.angerMakesDeluge = true ∧
  d.noOneAllowedOutAlive = true ∧
  d.savedManRejectedFromDeep = true ∧
  d.justWouldBeCutOff = true ∧
  d.faithfulWouldBeDestroyed = true

structure ResponsibilityGradient where
  sinnerOwnsSin : Bool := true
  evilDoerOwnsEvil : Bool := true
  justPrinceSpared : Bool := true
  faithfulSpared : Bool := true
  judgmentNotFlattened : Bool := true
deriving DecidableEq, Repr

def responsibilityGradient : ResponsibilityGradient := {}

def localResponsibilityPreserved (r : ResponsibilityGradient) : Prop :=
  r.sinnerOwnsSin = true ∧
  r.evilDoerOwnsEvil = true ∧
  r.justPrinceSpared = true ∧
  r.faithfulSpared = true ∧
  r.judgmentNotFlattened = true

structure BoundedCorrectionOperators where
  lionsReduceMen : Bool := true
  leopardsReduceMen : Bool := true
  famineDestroysCountry : Bool := true
  pestilenceDestroysMen : Bool := true
  alternativesReplaceDeluge : Bool := true
deriving DecidableEq, Repr

def boundedCorrectionOperators : BoundedCorrectionOperators := {}

def boundedCorrectionsReplaceReset (b : BoundedCorrectionOperators) : Prop :=
  b.lionsReduceMen = true ∧
  b.leopardsReduceMen = true ∧
  b.famineDestroysCountry = true ∧
  b.pestilenceDestroysMen = true ∧
  b.alternativesReplaceDeluge = true

structure CovenantAfterCorrection where
  judgmentAccomplished : Bool := true
  belRaisesSurvivorAndWife : Bool := true
  bondMade : Bool := true
  covenantEstablished : Bool := true
  blessingGiven : Bool := true
deriving DecidableEq, Repr

def covenantAfterCorrection : CovenantAfterCorrection := {}

def survivorCovenantRepair (c : CovenantAfterCorrection) : Prop :=
  c.judgmentAccomplished = true ∧
  c.belRaisesSurvivorAndWife = true ∧
  c.bondMade = true ∧
  c.covenantEstablished = true ∧
  c.blessingGiven = true

theorem hea_global_reset_overreaches :
    globalResetOverreaches delugeOverreach := by
  unfold globalResetOverreaches delugeOverreach
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem hea_local_responsibility_preserved :
    localResponsibilityPreserved responsibilityGradient := by
  unfold localResponsibilityPreserved responsibilityGradient
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem hea_bounded_corrections_replace_reset :
    boundedCorrectionsReplaceReset boundedCorrectionOperators := by
  unfold boundedCorrectionsReplaceReset boundedCorrectionOperators
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem hea_survivor_covenant_repair :
    survivorCovenantRepair covenantAfterCorrection := by
  unfold survivorCovenantRepair covenantAfterCorrection
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem hea_inherits_deluge_state_preservation :
    DelugeSeventhDayBirdProbeWitness.shipPreservesState
      DelugeSeventhDayBirdProbeWitness.sealedShipCarrier ∧
    survivorCovenantRepair covenantAfterCorrection := by
  exact ⟨DelugeSeventhDayBirdProbeWitness.deluge_ship_preserves_state,
    hea_survivor_covenant_repair⟩

theorem hea_pestilence_bridge_to_lubara :
    LubaraSevenWarriorGodsWitness.plagueProcessionWitness
      LubaraSevenWarriorGodsWitness.lubaraPlagueProcession ∧
    boundedCorrectionsReplaceReset boundedCorrectionOperators := by
  exact ⟨LubaraSevenWarriorGodsWitness.lubara_plague_procession,
    hea_bounded_corrections_replace_reset⟩

theorem hea_sea_reset_replaced_by_bounded_load :
    MummuTiamatuWaterChaosCarrierWitness.seaFriendFoeTaming
      MummuTiamatuWaterChaosCarrierWitness.seaTamingAmbivalence ∧
    globalResetOverreaches delugeOverreach ∧
    boundedCorrectionsReplaceReset boundedCorrectionOperators := by
  exact ⟨MummuTiamatuWaterChaosCarrierWitness.mummu_tiamatu_sea_friend_foe_taming,
    hea_global_reset_overreaches,
    hea_bounded_corrections_replace_reset⟩

theorem hea_alternative_judgment_witness :
    globalResetOverreaches delugeOverreach ∧
    localResponsibilityPreserved responsibilityGradient ∧
    boundedCorrectionsReplaceReset boundedCorrectionOperators ∧
    survivorCovenantRepair covenantAfterCorrection := by
  exact ⟨hea_global_reset_overreaches,
    hea_local_responsibility_preserved,
    hea_bounded_corrections_replace_reset,
    hea_survivor_covenant_repair⟩

end HeaAlternativeJudgmentWitness
end Gnosis.Witnesses.Chaldean
