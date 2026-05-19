import Init

namespace Gnosis.Witnesses.Bible.FirstCorinthians
namespace FirstCorinthiansCharityWitness

/-! # 1 Corinthians 13 -- Charity
Source text: `docs/ebooks/source-texts/bible-kjv.txt:92428-92463`. -/

structure CharityWitness where
  giftsWithoutCharityNothing : Bool
  charitySuffersLongKind : Bool
  charityDoesNotEnvyVauntPuff : Bool
  charitySeeksNotOwnNotProvoked : Bool
  charityRejoicesTruth : Bool
  charityBearsBelievesHopesEndures : Bool
  charityNeverFails : Bool
  partialGivesWayToPerfect : Bool
  faithHopeCharityRemainGreatestCharity : Bool
deriving DecidableEq, Repr

def charityWitness : CharityWitness where
  giftsWithoutCharityNothing := true
  charitySuffersLongKind := true
  charityDoesNotEnvyVauntPuff := true
  charitySeeksNotOwnNotProvoked := true
  charityRejoicesTruth := true
  charityBearsBelievesHopesEndures := true
  charityNeverFails := true
  partialGivesWayToPerfect := true
  faithHopeCharityRemainGreatestCharity := true

theorem first_corinthians_charity_witness :
    charityWitness.giftsWithoutCharityNothing = true
    ∧ charityWitness.charitySuffersLongKind = true
    ∧ charityWitness.charityDoesNotEnvyVauntPuff = true
    ∧ charityWitness.charitySeeksNotOwnNotProvoked = true
    ∧ charityWitness.charityRejoicesTruth = true
    ∧ charityWitness.charityBearsBelievesHopesEndures = true
    ∧ charityWitness.charityNeverFails = true
    ∧ charityWitness.partialGivesWayToPerfect = true
    ∧ charityWitness.faithHopeCharityRemainGreatestCharity = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end FirstCorinthiansCharityWitness
end Gnosis.Witnesses.Bible.FirstCorinthians
