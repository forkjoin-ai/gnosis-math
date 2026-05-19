import Gnosis.Witnesses.Hermetic.KybalionSevenPrinciplesWitness

namespace Gnosis.Witnesses.Hermetic

/-! Witness ledger for `kybalion-three-initiates.txt`, chapter 3. -/

structure MentalTransmutation where
  mindMayBeTransmuted : Bool := true
  trueTransmutationMentalArt : Bool := true
  innerKnowledgeComplementsOuter : Bool := true
  universeMentalEnablesConditionChange : Bool := true
  forceUsableInOppositeDirections : Bool := true
  polarityUnlocksTransmutation : Bool := true
  masterKeyGivesUnderlyingPrinciples : Bool := true
deriving Repr, DecidableEq

def mentalTransmutation : MentalTransmutation := {}

theorem kybalion_mental_transmutation_witness :
    mentalTransmutation.mindMayBeTransmuted = true ∧
      mentalTransmutation.trueTransmutationMentalArt = true ∧
      mentalTransmutation.innerKnowledgeComplementsOuter = true ∧
      mentalTransmutation.universeMentalEnablesConditionChange = true ∧
      mentalTransmutation.forceUsableInOppositeDirections = true ∧
      mentalTransmutation.polarityUnlocksTransmutation = true ∧
      mentalTransmutation.masterKeyGivesUnderlyingPrinciples = true := by
  simp [mentalTransmutation]

end Gnosis.Witnesses.Hermetic
