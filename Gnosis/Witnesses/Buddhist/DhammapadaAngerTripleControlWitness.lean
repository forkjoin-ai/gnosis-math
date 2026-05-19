import Gnosis.TruthOneManyNamesWitness

namespace Gnosis.Witnesses.Buddhist

/-! Witness ledger for Dhammapada chapter 17, "Anger". -/

structure AngerTripleControl where
  angerOvercomeByLove : Bool := true
  evilOvercomeByGood : Bool := true
  greedOvercomeByLiberality : Bool := true
  liarOvercomeByTruth : Bool := true
  nameFormNonAttachmentNoSuffering : Bool := true
  noUniversalPraiseBlame : Bool := true
  bodyAngerControlled : Bool := true
  tongueAngerControlled : Bool := true
  mindAngerControlled : Bool := true
  tripleControlComplete : Bool := true
deriving Repr, DecidableEq

def angerTripleControl : AngerTripleControl := {}

theorem dhammapada_anger_triple_control_witness :
    angerTripleControl.angerOvercomeByLove = true ∧
      angerTripleControl.evilOvercomeByGood = true ∧
      angerTripleControl.greedOvercomeByLiberality = true ∧
      angerTripleControl.liarOvercomeByTruth = true ∧
      angerTripleControl.nameFormNonAttachmentNoSuffering = true ∧
      angerTripleControl.noUniversalPraiseBlame = true ∧
      angerTripleControl.bodyAngerControlled = true ∧
      angerTripleControl.tongueAngerControlled = true ∧
      angerTripleControl.mindAngerControlled = true ∧
      angerTripleControl.tripleControlComplete = true := by
  simp [angerTripleControl]

end Gnosis.Witnesses.Buddhist
