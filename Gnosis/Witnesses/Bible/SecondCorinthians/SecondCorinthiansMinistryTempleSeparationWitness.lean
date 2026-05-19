import Init

namespace Gnosis.Witnesses.Bible.SecondCorinthians
namespace SecondCorinthiansMinistryTempleSeparationWitness

/-! # 2 Corinthians 6 -- Ministry Endurance, Enlarged Heart, and Temple Separation
Source text: `docs/ebooks/source-texts/bible-kjv.txt:93089-93129`. -/

structure MinistryTempleSeparation where
  receiveNotGraceInVain : Bool
  nowAcceptedTimeDaySalvation : Bool
  ministryNotBlamed : Bool
  ministersApprovedInEndurances : Bool
  purityKnowledgeHolyGhostLoveTruthPowerArmour : Bool
  paradoxesDyingYetLivePoorYetRich : Bool
  mouthOpenHeartEnlarged : Bool
  notUnequallyYoked : Bool
  templeLivingGod : Bool
  comeOutSeparateReceivedSonsDaughters : Bool
deriving DecidableEq, Repr

def ministryTempleSeparation : MinistryTempleSeparation where
  receiveNotGraceInVain := true
  nowAcceptedTimeDaySalvation := true
  ministryNotBlamed := true
  ministersApprovedInEndurances := true
  purityKnowledgeHolyGhostLoveTruthPowerArmour := true
  paradoxesDyingYetLivePoorYetRich := true
  mouthOpenHeartEnlarged := true
  notUnequallyYoked := true
  templeLivingGod := true
  comeOutSeparateReceivedSonsDaughters := true

theorem second_corinthians_ministry_temple_separation_witness :
    ministryTempleSeparation.receiveNotGraceInVain = true
    ∧ ministryTempleSeparation.nowAcceptedTimeDaySalvation = true
    ∧ ministryTempleSeparation.ministryNotBlamed = true
    ∧ ministryTempleSeparation.ministersApprovedInEndurances = true
    ∧ ministryTempleSeparation.purityKnowledgeHolyGhostLoveTruthPowerArmour = true
    ∧ ministryTempleSeparation.paradoxesDyingYetLivePoorYetRich = true
    ∧ ministryTempleSeparation.mouthOpenHeartEnlarged = true
    ∧ ministryTempleSeparation.notUnequallyYoked = true
    ∧ ministryTempleSeparation.templeLivingGod = true
    ∧ ministryTempleSeparation.comeOutSeparateReceivedSonsDaughters = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end SecondCorinthiansMinistryTempleSeparationWitness
end Gnosis.Witnesses.Bible.SecondCorinthians
