import Gnosis.Witnesses.Hermetic.KybalionMentalGenderWitness

namespace Gnosis.Witnesses.Hermetic

/-! Witness ledger for `kybalion-three-initiates.txt`, chapter 15. -/

structure FinalMaximsUse where
  knowledgeRequiresUse : Bool := true
  mentalMiserlinessRejected : Bool := true
  willDirectsAttention : Bool := true
  attentionChangesVibration : Bool := true
  oppositePoleSuppressesUndesired : Bool := true
  rhythmNeutralizedByPolarization : Bool := true
  principleCounterbalancedNotDestroyed : Bool := true
  higherCausationOvercomesLower : Bool := true
  playersNotPawns : Bool := true
  transmutationMentalArt : Bool := true
  universeMental : Bool := true
deriving Repr, DecidableEq

def finalMaximsUse : FinalMaximsUse := {}

theorem kybalion_final_maxims_use_witness :
    finalMaximsUse.knowledgeRequiresUse = true ∧
      finalMaximsUse.mentalMiserlinessRejected = true ∧
      finalMaximsUse.willDirectsAttention = true ∧
      finalMaximsUse.attentionChangesVibration = true ∧
      finalMaximsUse.oppositePoleSuppressesUndesired = true ∧
      finalMaximsUse.rhythmNeutralizedByPolarization = true ∧
      finalMaximsUse.principleCounterbalancedNotDestroyed = true ∧
      finalMaximsUse.higherCausationOvercomesLower = true ∧
      finalMaximsUse.playersNotPawns = true ∧
      finalMaximsUse.transmutationMentalArt = true ∧
      finalMaximsUse.universeMental = true := by
  simp [finalMaximsUse]

end Gnosis.Witnesses.Hermetic
