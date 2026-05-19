import Init

namespace Gnosis.Witnesses.Bible.SecondCorinthians
namespace SecondCorinthiansWeaknessStrengthEdifyingWitness

/-! # 2 Corinthians 12 -- Weakness, Grace, and Edifying Concern
Source text: `docs/ebooks/source-texts/bible-kjv.txt:93455-93525`. -/

structure WeaknessStrengthEdifying where
  visionsRevelationsThirdHeavenParadise : Bool
  thornGivenLestExalted : Bool
  graceSufficientStrengthPerfectWeakness : Bool
  gloryInInfirmitiesPowerChristRest : Bool
  weakThenStrong : Bool
  signsApostlePatienceWondersMightyDeeds : Bool
  seekYouNotYoursSpendAndBeSpent : Bool
  titusSameSpiritSteps : Bool
  allThingsForEdifying : Bool
  fearDebatesEnvyingsUnrepentedSins : Bool
deriving DecidableEq, Repr

def weaknessStrengthEdifying : WeaknessStrengthEdifying where
  visionsRevelationsThirdHeavenParadise := true
  thornGivenLestExalted := true
  graceSufficientStrengthPerfectWeakness := true
  gloryInInfirmitiesPowerChristRest := true
  weakThenStrong := true
  signsApostlePatienceWondersMightyDeeds := true
  seekYouNotYoursSpendAndBeSpent := true
  titusSameSpiritSteps := true
  allThingsForEdifying := true
  fearDebatesEnvyingsUnrepentedSins := true

theorem second_corinthians_weakness_strength_edifying_witness :
    weaknessStrengthEdifying.visionsRevelationsThirdHeavenParadise = true
    ∧ weaknessStrengthEdifying.thornGivenLestExalted = true
    ∧ weaknessStrengthEdifying.graceSufficientStrengthPerfectWeakness = true
    ∧ weaknessStrengthEdifying.gloryInInfirmitiesPowerChristRest = true
    ∧ weaknessStrengthEdifying.weakThenStrong = true
    ∧ weaknessStrengthEdifying.signsApostlePatienceWondersMightyDeeds = true
    ∧ weaknessStrengthEdifying.seekYouNotYoursSpendAndBeSpent = true
    ∧ weaknessStrengthEdifying.titusSameSpiritSteps = true
    ∧ weaknessStrengthEdifying.allThingsForEdifying = true
    ∧ weaknessStrengthEdifying.fearDebatesEnvyingsUnrepentedSins = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end SecondCorinthiansWeaknessStrengthEdifyingWitness
end Gnosis.Witnesses.Bible.SecondCorinthians
