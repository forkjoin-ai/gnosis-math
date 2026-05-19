import Init

namespace Gnosis.Witnesses.Bible.FirstCorinthians
namespace FirstCorinthiansProphecyOrderWitness

/-! # 1 Corinthians 14 -- Prophecy, Tongues, and Order
Source text: `docs/ebooks/source-texts/bible-kjv.txt:92465-92582`. -/

structure ProphecyOrder where
  followCharityDesireGiftsProphesy : Bool
  prophecyEdifiesExhortsComforts : Bool
  tonguesNeedInterpretationForChurch : Bool
  understandingBetterThanUnknownWords : Bool
  unbelieversSignAndProphecyConviction : Bool
  allThingsUntoEdifying : Bool
  prophetsSubjectToProphets : Bool
  godNotConfusionButPeace : Bool
  covetProphesyForbidNotTongues : Bool
  decentlyAndInOrder : Bool
deriving DecidableEq, Repr

def prophecyOrder : ProphecyOrder where
  followCharityDesireGiftsProphesy := true
  prophecyEdifiesExhortsComforts := true
  tonguesNeedInterpretationForChurch := true
  understandingBetterThanUnknownWords := true
  unbelieversSignAndProphecyConviction := true
  allThingsUntoEdifying := true
  prophetsSubjectToProphets := true
  godNotConfusionButPeace := true
  covetProphesyForbidNotTongues := true
  decentlyAndInOrder := true

theorem first_corinthians_prophecy_order_witness :
    prophecyOrder.followCharityDesireGiftsProphesy = true
    ∧ prophecyOrder.prophecyEdifiesExhortsComforts = true
    ∧ prophecyOrder.tonguesNeedInterpretationForChurch = true
    ∧ prophecyOrder.understandingBetterThanUnknownWords = true
    ∧ prophecyOrder.unbelieversSignAndProphecyConviction = true
    ∧ prophecyOrder.allThingsUntoEdifying = true
    ∧ prophecyOrder.prophetsSubjectToProphets = true
    ∧ prophecyOrder.godNotConfusionButPeace = true
    ∧ prophecyOrder.covetProphesyForbidNotTongues = true
    ∧ prophecyOrder.decentlyAndInOrder = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end FirstCorinthiansProphecyOrderWitness
end Gnosis.Witnesses.Bible.FirstCorinthians
