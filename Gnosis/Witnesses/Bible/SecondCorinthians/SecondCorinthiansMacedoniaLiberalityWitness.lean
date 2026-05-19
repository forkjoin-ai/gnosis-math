import Init

namespace Gnosis.Witnesses.Bible.SecondCorinthians
namespace SecondCorinthiansMacedoniaLiberalityWitness

/-! # 2 Corinthians 8 -- Macedonia, Equality, and Honest Administration
Source text: `docs/ebooks/source-texts/bible-kjv.txt:93190-93258`. -/

structure MacedoniaLiberality where
  macedoniaGraceJoyPovertyLiberality : Bool
  beyondPowerWillingFellowshipSaints : Bool
  firstGaveSelvesToLord : Bool
  aboundInThisGraceAlso : Bool
  christRichBecamePoor : Bool
  willingMindAcceptedAccordingToHave : Bool
  equalitySupplyWant : Bool
  titusEarnestCare : Bool
  honestThingsLordAndMen : Bool
  messengersChurchesGloryChrist : Bool
deriving DecidableEq, Repr

def macedoniaLiberality : MacedoniaLiberality where
  macedoniaGraceJoyPovertyLiberality := true
  beyondPowerWillingFellowshipSaints := true
  firstGaveSelvesToLord := true
  aboundInThisGraceAlso := true
  christRichBecamePoor := true
  willingMindAcceptedAccordingToHave := true
  equalitySupplyWant := true
  titusEarnestCare := true
  honestThingsLordAndMen := true
  messengersChurchesGloryChrist := true

theorem second_corinthians_macedonia_liberality_witness :
    macedoniaLiberality.macedoniaGraceJoyPovertyLiberality = true
    ∧ macedoniaLiberality.beyondPowerWillingFellowshipSaints = true
    ∧ macedoniaLiberality.firstGaveSelvesToLord = true
    ∧ macedoniaLiberality.aboundInThisGraceAlso = true
    ∧ macedoniaLiberality.christRichBecamePoor = true
    ∧ macedoniaLiberality.willingMindAcceptedAccordingToHave = true
    ∧ macedoniaLiberality.equalitySupplyWant = true
    ∧ macedoniaLiberality.titusEarnestCare = true
    ∧ macedoniaLiberality.honestThingsLordAndMen = true
    ∧ macedoniaLiberality.messengersChurchesGloryChrist = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end SecondCorinthiansMacedoniaLiberalityWitness
end Gnosis.Witnesses.Bible.SecondCorinthians
