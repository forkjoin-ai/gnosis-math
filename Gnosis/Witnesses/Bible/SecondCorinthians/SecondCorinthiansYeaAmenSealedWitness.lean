import Init

namespace Gnosis.Witnesses.Bible.SecondCorinthians
namespace SecondCorinthiansYeaAmenSealedWitness

/-! # 2 Corinthians 1:15-24 -- Yea, Amen, Sealed, Helpers of Joy
Source text: `docs/ebooks/source-texts/bible-kjv.txt:92852-92877`. -/

structure YeaAmenSealed where
  intendedSecondBenefitTravel : Bool
  wordNotYeaAndNay : Bool
  sonOfGodInHimYea : Bool
  promisesYeaAmenInChrist : Bool
  establishedAnointedByGod : Bool
  sealedEarnestSpiritHearts : Bool
  sparedCorinth : Bool
  notDominionOverFaithHelpersJoy : Bool
  byFaithStand : Bool
deriving DecidableEq, Repr

def yeaAmenSealed : YeaAmenSealed where
  intendedSecondBenefitTravel := true
  wordNotYeaAndNay := true
  sonOfGodInHimYea := true
  promisesYeaAmenInChrist := true
  establishedAnointedByGod := true
  sealedEarnestSpiritHearts := true
  sparedCorinth := true
  notDominionOverFaithHelpersJoy := true
  byFaithStand := true

theorem second_corinthians_yea_amen_sealed_witness :
    yeaAmenSealed.intendedSecondBenefitTravel = true
    ∧ yeaAmenSealed.wordNotYeaAndNay = true
    ∧ yeaAmenSealed.sonOfGodInHimYea = true
    ∧ yeaAmenSealed.promisesYeaAmenInChrist = true
    ∧ yeaAmenSealed.establishedAnointedByGod = true
    ∧ yeaAmenSealed.sealedEarnestSpiritHearts = true
    ∧ yeaAmenSealed.sparedCorinth = true
    ∧ yeaAmenSealed.notDominionOverFaithHelpersJoy = true
    ∧ yeaAmenSealed.byFaithStand = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end SecondCorinthiansYeaAmenSealedWitness
end Gnosis.Witnesses.Bible.SecondCorinthians
