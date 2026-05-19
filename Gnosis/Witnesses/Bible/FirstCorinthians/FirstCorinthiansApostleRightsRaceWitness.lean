import Init

namespace Gnosis.Witnesses.Bible.FirstCorinthians
namespace FirstCorinthiansApostleRightsRaceWitness

/-! # 1 Corinthians 9 -- Apostle Rights, Gospel Servanthood, and Race
Source text: `docs/ebooks/source-texts/bible-kjv.txt:92096-92164`. -/

structure ApostleRightsRace where
  apostleshipSealInLord : Bool
  rightToEatDrinkAndSupport : Bool
  notUsingPowerLestHinderGospel : Bool
  preachGospelWithoutCharge : Bool
  servantToAllToGainMore : Bool
  allThingsToAllToSaveSome : Bool
  runToObtainIncorruptibleCrown : Bool
  keepBodyInSubjection : Bool
deriving DecidableEq, Repr

def apostleRightsRace : ApostleRightsRace where
  apostleshipSealInLord := true
  rightToEatDrinkAndSupport := true
  notUsingPowerLestHinderGospel := true
  preachGospelWithoutCharge := true
  servantToAllToGainMore := true
  allThingsToAllToSaveSome := true
  runToObtainIncorruptibleCrown := true
  keepBodyInSubjection := true

theorem first_corinthians_apostle_rights_race_witness :
    apostleRightsRace.apostleshipSealInLord = true
    ∧ apostleRightsRace.rightToEatDrinkAndSupport = true
    ∧ apostleRightsRace.notUsingPowerLestHinderGospel = true
    ∧ apostleRightsRace.preachGospelWithoutCharge = true
    ∧ apostleRightsRace.servantToAllToGainMore = true
    ∧ apostleRightsRace.allThingsToAllToSaveSome = true
    ∧ apostleRightsRace.runToObtainIncorruptibleCrown = true
    ∧ apostleRightsRace.keepBodyInSubjection = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end FirstCorinthiansApostleRightsRaceWitness
end Gnosis.Witnesses.Bible.FirstCorinthians
