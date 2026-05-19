import Init

namespace Gnosis.Witnesses.Bible.FirstCorinthians
namespace FirstCorinthiansMarriageCallingWitness

/-! # 1 Corinthians 7 -- Marriage, Calling, and Present Distress
Source text: `docs/ebooks/source-texts/bible-kjv.txt:91932-92057`. -/

structure MarriageCalling where
  mutualMarriageDuty : Bool
  giftAndContainmentCounsel : Bool
  marriedNotDepart : Bool
  unbelievingSpouseSanctifiedHousehold : Bool
  godCalledToPeace : Bool
  abideInCalling : Bool
  timeShortPresentDistress : Bool
  unmarriedCareForLord : Bool
  widowFreeOnlyInLord : Bool
deriving DecidableEq, Repr

def marriageCalling : MarriageCalling where
  mutualMarriageDuty := true
  giftAndContainmentCounsel := true
  marriedNotDepart := true
  unbelievingSpouseSanctifiedHousehold := true
  godCalledToPeace := true
  abideInCalling := true
  timeShortPresentDistress := true
  unmarriedCareForLord := true
  widowFreeOnlyInLord := true

theorem first_corinthians_marriage_calling_witness :
    marriageCalling.mutualMarriageDuty = true
    ∧ marriageCalling.giftAndContainmentCounsel = true
    ∧ marriageCalling.marriedNotDepart = true
    ∧ marriageCalling.unbelievingSpouseSanctifiedHousehold = true
    ∧ marriageCalling.godCalledToPeace = true
    ∧ marriageCalling.abideInCalling = true
    ∧ marriageCalling.timeShortPresentDistress = true
    ∧ marriageCalling.unmarriedCareForLord = true
    ∧ marriageCalling.widowFreeOnlyInLord = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end FirstCorinthiansMarriageCallingWitness
end Gnosis.Witnesses.Bible.FirstCorinthians
