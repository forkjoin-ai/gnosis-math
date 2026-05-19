import Init

namespace Gnosis.Witnesses.Bible.FirstCorinthians
namespace FirstCorinthiansSpiritPowerWisdomWitness

/-! # 1 Corinthians 2 -- Spirit, Power, and Hidden Wisdom
Source text: `docs/ebooks/source-texts/bible-kjv.txt:91671-91718`. -/

structure SpiritPowerWisdom where
  notExcellencyOfSpeech : Bool
  christCrucifiedKnown : Bool
  demonstrationSpiritPower : Bool
  faithStandsInPowerOfGod : Bool
  wisdomOfGodInMystery : Bool
  spiritSearchesDeepThings : Bool
  spiritualThingsSpirituallyDiscerned : Bool
  mindOfChrist : Bool
deriving DecidableEq, Repr

def spiritPowerWisdom : SpiritPowerWisdom where
  notExcellencyOfSpeech := true
  christCrucifiedKnown := true
  demonstrationSpiritPower := true
  faithStandsInPowerOfGod := true
  wisdomOfGodInMystery := true
  spiritSearchesDeepThings := true
  spiritualThingsSpirituallyDiscerned := true
  mindOfChrist := true

theorem first_corinthians_spirit_power_wisdom_witness :
    spiritPowerWisdom.notExcellencyOfSpeech = true
    ∧ spiritPowerWisdom.christCrucifiedKnown = true
    ∧ spiritPowerWisdom.demonstrationSpiritPower = true
    ∧ spiritPowerWisdom.faithStandsInPowerOfGod = true
    ∧ spiritPowerWisdom.wisdomOfGodInMystery = true
    ∧ spiritPowerWisdom.spiritSearchesDeepThings = true
    ∧ spiritPowerWisdom.spiritualThingsSpirituallyDiscerned = true
    ∧ spiritPowerWisdom.mindOfChrist = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end FirstCorinthiansSpiritPowerWisdomWitness
end Gnosis.Witnesses.Bible.FirstCorinthians
