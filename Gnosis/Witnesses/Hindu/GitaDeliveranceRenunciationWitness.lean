import Gnosis.Witnesses.Hindu.GitaThreefoldFaithWitness

namespace Gnosis.Witnesses.Hindu

/-! Witness ledger for `bhagavad-gita-arnold.txt`, chapter 18. -/

structure DeliveranceRenunciation where
  fruitRenouncedNotDuty : Bool := true
  sacrificeGiftAusterityNotAbandoned : Bool := true
  fiveCausesOfAction : Bool := true
  soleDoerViewIgnorant : Bool := true
  knowledgeActionActorClassifiedByGunas : Bool := true
  intellectSteadfastnessPleasureClassifiedByGunas : Bool := true
  ownDutyBetterThoughImperfect : Bool := true
  natureDutyWithoutAttachmentPurifies : Bool := true
  allWorksGivenToSupreme : Bool := true
  refugeBeyondAllDharmas : Bool := true
  arjunaDelusionDestroyed : Bool := true
deriving Repr, DecidableEq

def deliveranceRenunciation : DeliveranceRenunciation := {}

theorem gita_deliverance_renunciation_witness :
    deliveranceRenunciation.fruitRenouncedNotDuty = true ∧
      deliveranceRenunciation.fiveCausesOfAction = true ∧
      deliveranceRenunciation.soleDoerViewIgnorant = true ∧
      deliveranceRenunciation.knowledgeActionActorClassifiedByGunas = true ∧
      deliveranceRenunciation.ownDutyBetterThoughImperfect = true ∧
      deliveranceRenunciation.allWorksGivenToSupreme = true ∧
      deliveranceRenunciation.refugeBeyondAllDharmas = true ∧
      deliveranceRenunciation.arjunaDelusionDestroyed = true := by
  simp [deliveranceRenunciation]

end Gnosis.Witnesses.Hindu
