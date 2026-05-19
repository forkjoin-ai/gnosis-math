import Gnosis.BuddhistAttachmentSkyrms

namespace Gnosis.Witnesses.Buddhist

/-!
# Dhammapada Impurity Root Witness

Witness ledger for `docs/ebooks/source-texts/dhammapada-muller.txt`,
chapter 18, "Impurity".
-/

structure IslandAgainstImpurity where
  deathMessengersNear : Bool := true
  noProvisionForJourney : Bool := true
  makeSelfIsland : Bool := true
  impuritiesBlownAway : Bool := true
  noBirthDecayReturn : Bool := true
  silverPurifiedLittleByLittle : Bool := true
deriving Repr, DecidableEq

structure TaintRoot where
  ironImpurityDestroysIron : Bool := true
  ownWorksLeadEvilPath : Bool := true
  slothTaintsBody : Bool := true
  thoughtlessnessTaintsWatchman : Bool := true
  ignoranceGreatestTaint : Bool := true
  taintThrownOff : Bool := true
deriving Repr, DecidableEq

structure FaultAttention where
  viceDigsOwnRoot : Bool := true
  greedViceBringLongGrief : Bool := true
  jealousyOverGiftsNoRest : Bool := true
  rootedFeelingDestroyedFindsRest : Bool := true
  ownFaultHardToSee : Bool := true
  othersFaultsIncreasePassions : Bool := true
  outwardActsDoNotMakeSamana : Bool := true
  awakenedNeverShaken : Bool := true
deriving Repr, DecidableEq

def islandAgainstImpurity : IslandAgainstImpurity := {}
def taintRoot : TaintRoot := {}
def faultAttention : FaultAttention := {}

theorem dhammapada_island_against_impurity :
    islandAgainstImpurity.deathMessengersNear = true ∧
      islandAgainstImpurity.noProvisionForJourney = true ∧
      islandAgainstImpurity.makeSelfIsland = true ∧
      islandAgainstImpurity.impuritiesBlownAway = true ∧
      islandAgainstImpurity.noBirthDecayReturn = true ∧
      islandAgainstImpurity.silverPurifiedLittleByLittle = true := by
  simp [islandAgainstImpurity]

theorem dhammapada_taint_root :
    taintRoot.ironImpurityDestroysIron = true ∧
      taintRoot.ownWorksLeadEvilPath = true ∧
      taintRoot.slothTaintsBody = true ∧
      taintRoot.thoughtlessnessTaintsWatchman = true ∧
      taintRoot.ignoranceGreatestTaint = true ∧
      taintRoot.taintThrownOff = true := by
  simp [taintRoot]

theorem dhammapada_fault_attention :
    faultAttention.viceDigsOwnRoot = true ∧
      faultAttention.greedViceBringLongGrief = true ∧
      faultAttention.jealousyOverGiftsNoRest = true ∧
      faultAttention.rootedFeelingDestroyedFindsRest = true ∧
      faultAttention.ownFaultHardToSee = true ∧
      faultAttention.othersFaultsIncreasePassions = true ∧
      faultAttention.outwardActsDoNotMakeSamana = true ∧
      faultAttention.awakenedNeverShaken = true := by
  simp [faultAttention]

theorem dhammapada_impurity_root_witness :
    islandAgainstImpurity.makeSelfIsland = true ∧
      islandAgainstImpurity.noBirthDecayReturn = true ∧
      taintRoot.ignoranceGreatestTaint = true ∧
      faultAttention.viceDigsOwnRoot = true ∧
      faultAttention.ownFaultHardToSee = true ∧
      faultAttention.othersFaultsIncreasePassions = true ∧
      faultAttention.outwardActsDoNotMakeSamana = true := by
  simp [islandAgainstImpurity, taintRoot, faultAttention]

end Gnosis.Witnesses.Buddhist
