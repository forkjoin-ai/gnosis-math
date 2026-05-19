import Init

namespace Gnosis.Witnesses.Bible.FirstCorinthians
namespace FirstCorinthiansResurrectionVictoryWitness

/-! # 1 Corinthians 15 -- Gospel, Resurrection, and Victory
Source text: `docs/ebooks/source-texts/bible-kjv.txt:92584-92735`. -/

structure ResurrectionVictory where
  gospelReceivedStandSaved : Bool
  christDiedBuriedRoseAccordingScriptures : Bool
  witnessesOfRisenChrist : Bool
  ifNoResurrectionPreachingFaithVain : Bool
  christFirstfruits : Bool
  adamDeathChristLife : Bool
  lastEnemyDeathDestroyed : Bool
  resurrectionBodySpiritualIncorruptible : Bool
  deathSwallowedVictory : Bool
  steadfastAboundingLordLabourNotVain : Bool
deriving DecidableEq, Repr

def resurrectionVictory : ResurrectionVictory where
  gospelReceivedStandSaved := true
  christDiedBuriedRoseAccordingScriptures := true
  witnessesOfRisenChrist := true
  ifNoResurrectionPreachingFaithVain := true
  christFirstfruits := true
  adamDeathChristLife := true
  lastEnemyDeathDestroyed := true
  resurrectionBodySpiritualIncorruptible := true
  deathSwallowedVictory := true
  steadfastAboundingLordLabourNotVain := true

theorem first_corinthians_resurrection_victory_witness :
    resurrectionVictory.gospelReceivedStandSaved = true
    ∧ resurrectionVictory.christDiedBuriedRoseAccordingScriptures = true
    ∧ resurrectionVictory.witnessesOfRisenChrist = true
    ∧ resurrectionVictory.ifNoResurrectionPreachingFaithVain = true
    ∧ resurrectionVictory.christFirstfruits = true
    ∧ resurrectionVictory.adamDeathChristLife = true
    ∧ resurrectionVictory.lastEnemyDeathDestroyed = true
    ∧ resurrectionVictory.resurrectionBodySpiritualIncorruptible = true
    ∧ resurrectionVictory.deathSwallowedVictory = true
    ∧ resurrectionVictory.steadfastAboundingLordLabourNotVain = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end FirstCorinthiansResurrectionVictoryWitness
end Gnosis.Witnesses.Bible.FirstCorinthians
