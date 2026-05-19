import Gnosis.GnosisTriptychBraid

namespace Gnosis.Witnesses.Buddhist

/-!
# Dhammapada Earnest Island Witness

Witness ledger for `docs/ebooks/source-texts/dhammapada-muller.txt`,
chapter 2, "On Earnestness".

Earnestness functions as a flood-proof runtime island: rousing, restraint,
reflection, and watchfulness burn fetters and prevent falling away.
-/

structure DeathlessEarnestness where
  earnestnessPathImmortality : Bool := true
  thoughtlessnessPathDeath : Bool := true
  earnestDoNotDie : Bool := true
  thoughtlessDeadAlready : Bool := true
  meditativeSteadyAttainNirvana : Bool := true
deriving Repr, DecidableEq

structure FloodProofIsland where
  rousedNotForgetful : Bool := true
  pureDeedsConsiderateAction : Bool := true
  restraintControlLaw : Bool := true
  islandNoFloodOverwhelms : Bool := true
  vanityDrivenAwayByEarnestness : Bool := true
  mountainViewOverFools : Bool := true
deriving Repr, DecidableEq

structure WakefulFetterBurning where
  awakeAmongSleepers : Bool := true
  racerLeavesHackBehind : Bool := true
  earnestnessPraised : Bool := true
  fireBurnsFetters : Bool := true
  reflectionPreventsFallAway : Bool := true
  closeUponNirvana : Bool := true
deriving Repr, DecidableEq

def deathlessEarnestness : DeathlessEarnestness := {}
def floodProofIsland : FloodProofIsland := {}
def wakefulFetterBurning : WakefulFetterBurning := {}

theorem dhammapada_deathless_earnestness :
    deathlessEarnestness.earnestnessPathImmortality = true ∧
      deathlessEarnestness.thoughtlessnessPathDeath = true ∧
      deathlessEarnestness.earnestDoNotDie = true ∧
      deathlessEarnestness.thoughtlessDeadAlready = true ∧
      deathlessEarnestness.meditativeSteadyAttainNirvana = true := by
  simp [deathlessEarnestness]

theorem dhammapada_flood_proof_island :
    floodProofIsland.rousedNotForgetful = true ∧
      floodProofIsland.pureDeedsConsiderateAction = true ∧
      floodProofIsland.restraintControlLaw = true ∧
      floodProofIsland.islandNoFloodOverwhelms = true ∧
      floodProofIsland.vanityDrivenAwayByEarnestness = true ∧
      floodProofIsland.mountainViewOverFools = true := by
  simp [floodProofIsland]

theorem dhammapada_wakeful_fetter_burning :
    wakefulFetterBurning.awakeAmongSleepers = true ∧
      wakefulFetterBurning.racerLeavesHackBehind = true ∧
      wakefulFetterBurning.earnestnessPraised = true ∧
      wakefulFetterBurning.fireBurnsFetters = true ∧
      wakefulFetterBurning.reflectionPreventsFallAway = true ∧
      wakefulFetterBurning.closeUponNirvana = true := by
  simp [wakefulFetterBurning]

theorem dhammapada_earnest_island_witness :
    deathlessEarnestness.earnestnessPathImmortality = true ∧
      deathlessEarnestness.thoughtlessnessPathDeath = true ∧
      floodProofIsland.islandNoFloodOverwhelms = true ∧
      wakefulFetterBurning.awakeAmongSleepers = true ∧
      wakefulFetterBurning.fireBurnsFetters = true ∧
      wakefulFetterBurning.reflectionPreventsFallAway = true := by
  simp [deathlessEarnestness, floodProofIsland, wakefulFetterBurning]

end Gnosis.Witnesses.Buddhist
