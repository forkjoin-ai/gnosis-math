import Gnosis.Witnesses.Hindu.GitaImperishableYogaWitness

namespace Gnosis.Witnesses.Hindu

/-! Witness ledger for `bhagavad-gita-arnold.txt`, chapter 13. -/

structure FieldKnower where
  bodyAsField : Bool := true
  knowerOfFieldDistinct : Bool := true
  humilityNonAttachmentCountAsKnowledge : Bool := true
  knowledgeOppositeIsIgnorance : Bool := true
  paraBrahmBeyondSatAsat : Bool := true
  natureActsThroughQualities : Bool := true
  soulWitnessPermitterSustainer : Bool := true
  sameLordInPerishingForms : Bool := true
  seeingActionsAsNatureFrees : Bool := true
  fieldKnowerDifferenceLiberates : Bool := true
deriving Repr, DecidableEq

def fieldKnower : FieldKnower := {}

theorem gita_field_knower_witness :
    fieldKnower.bodyAsField = true ∧
      fieldKnower.knowerOfFieldDistinct = true ∧
      fieldKnower.humilityNonAttachmentCountAsKnowledge = true ∧
      fieldKnower.paraBrahmBeyondSatAsat = true ∧
      fieldKnower.natureActsThroughQualities = true ∧
      fieldKnower.soulWitnessPermitterSustainer = true ∧
      fieldKnower.sameLordInPerishingForms = true ∧
      fieldKnower.fieldKnowerDifferenceLiberates = true := by
  simp [fieldKnower]

end Gnosis.Witnesses.Hindu
