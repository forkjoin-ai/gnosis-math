import Init

namespace Gnosis.Witnesses.Bible.FirstCorinthians
namespace FirstCorinthiansGiftsBodyWitness

/-! # 1 Corinthians 12 -- Gifts, One Spirit, and One Body
Source text: `docs/ebooks/source-texts/bible-kjv.txt:92351-92426`. -/

structure GiftsBody where
  jesusLordByHolyGhost : Bool
  diversitiesSameSpiritLordGod : Bool
  manifestationGivenToProfit : Bool
  manyGiftsOneSpirit : Bool
  oneBodyManyMembers : Bool
  baptizedIntoOneBody : Bool
  membersNeedOneAnother : Bool
  godSetMembersAndTemperedBody : Bool
  bodyOfChristMembersInParticular : Bool
  covetBestGiftsMoreExcellentWay : Bool
deriving DecidableEq, Repr

def giftsBody : GiftsBody where
  jesusLordByHolyGhost := true
  diversitiesSameSpiritLordGod := true
  manifestationGivenToProfit := true
  manyGiftsOneSpirit := true
  oneBodyManyMembers := true
  baptizedIntoOneBody := true
  membersNeedOneAnother := true
  godSetMembersAndTemperedBody := true
  bodyOfChristMembersInParticular := true
  covetBestGiftsMoreExcellentWay := true

theorem first_corinthians_gifts_body_witness :
    giftsBody.jesusLordByHolyGhost = true
    ∧ giftsBody.diversitiesSameSpiritLordGod = true
    ∧ giftsBody.manifestationGivenToProfit = true
    ∧ giftsBody.manyGiftsOneSpirit = true
    ∧ giftsBody.oneBodyManyMembers = true
    ∧ giftsBody.baptizedIntoOneBody = true
    ∧ giftsBody.membersNeedOneAnother = true
    ∧ giftsBody.godSetMembersAndTemperedBody = true
    ∧ giftsBody.bodyOfChristMembersInParticular = true
    ∧ giftsBody.covetBestGiftsMoreExcellentWay = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end FirstCorinthiansGiftsBodyWitness
end Gnosis.Witnesses.Bible.FirstCorinthians
