import Init

namespace Gnosis.Witnesses.Bible.SecondCorinthians
namespace SecondCorinthiansEpistleSpiritLibertyWitness

/-! # 2 Corinthians 3 -- Epistle, Spirit, Liberty, and Transformation
Source text: `docs/ebooks/source-texts/bible-kjv.txt:92929-92975`. -/

structure EpistleSpiritLiberty where
  corinthiansEpistleWrittenInHearts : Bool
  epistleOfChristSpiritLivingGod : Bool
  sufficiencyOfGod : Bool
  ableMinistersNewTestamentSpiritGivesLife : Bool
  ministrationSpiritRighteousnessExceedsGlory : Bool
  hopeGreatPlainnessSpeech : Bool
  veilDoneAwayInChrist : Bool
  turnToLordVeilTakenAway : Bool
  spiritOfLordLiberty : Bool
  changedGloryToGloryBySpirit : Bool
deriving DecidableEq, Repr

def epistleSpiritLiberty : EpistleSpiritLiberty where
  corinthiansEpistleWrittenInHearts := true
  epistleOfChristSpiritLivingGod := true
  sufficiencyOfGod := true
  ableMinistersNewTestamentSpiritGivesLife := true
  ministrationSpiritRighteousnessExceedsGlory := true
  hopeGreatPlainnessSpeech := true
  veilDoneAwayInChrist := true
  turnToLordVeilTakenAway := true
  spiritOfLordLiberty := true
  changedGloryToGloryBySpirit := true

theorem second_corinthians_epistle_spirit_liberty_witness :
    epistleSpiritLiberty.corinthiansEpistleWrittenInHearts = true
    ∧ epistleSpiritLiberty.epistleOfChristSpiritLivingGod = true
    ∧ epistleSpiritLiberty.sufficiencyOfGod = true
    ∧ epistleSpiritLiberty.ableMinistersNewTestamentSpiritGivesLife = true
    ∧ epistleSpiritLiberty.ministrationSpiritRighteousnessExceedsGlory = true
    ∧ epistleSpiritLiberty.hopeGreatPlainnessSpeech = true
    ∧ epistleSpiritLiberty.veilDoneAwayInChrist = true
    ∧ epistleSpiritLiberty.turnToLordVeilTakenAway = true
    ∧ epistleSpiritLiberty.spiritOfLordLiberty = true
    ∧ epistleSpiritLiberty.changedGloryToGloryBySpirit = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end SecondCorinthiansEpistleSpiritLibertyWitness
end Gnosis.Witnesses.Bible.SecondCorinthians
