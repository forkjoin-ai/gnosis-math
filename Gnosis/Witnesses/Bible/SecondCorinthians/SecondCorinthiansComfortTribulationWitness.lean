import Init

namespace Gnosis.Witnesses.Bible.SecondCorinthians
namespace SecondCorinthiansComfortTribulationWitness

/-! # 2 Corinthians 1:3-7 -- Comfort in Tribulation
Source text: `docs/ebooks/source-texts/bible-kjv.txt:92815-92830`. -/

structure ComfortTribulation where
  fatherMerciesGodAllComfort : Bool
  comfortedToComfortOthers : Bool
  sufferingsOfChristAbound : Bool
  consolationAboundsByChrist : Bool
  afflictionForConsolationSalvation : Bool
  comfortForConsolationSalvation : Bool
  hopeStedfastPartakersSufferingsConsolation : Bool
deriving DecidableEq, Repr

def comfortTribulation : ComfortTribulation where
  fatherMerciesGodAllComfort := true
  comfortedToComfortOthers := true
  sufferingsOfChristAbound := true
  consolationAboundsByChrist := true
  afflictionForConsolationSalvation := true
  comfortForConsolationSalvation := true
  hopeStedfastPartakersSufferingsConsolation := true

theorem second_corinthians_comfort_tribulation_witness :
    comfortTribulation.fatherMerciesGodAllComfort = true
    ∧ comfortTribulation.comfortedToComfortOthers = true
    ∧ comfortTribulation.sufferingsOfChristAbound = true
    ∧ comfortTribulation.consolationAboundsByChrist = true
    ∧ comfortTribulation.afflictionForConsolationSalvation = true
    ∧ comfortTribulation.comfortForConsolationSalvation = true
    ∧ comfortTribulation.hopeStedfastPartakersSufferingsConsolation = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end SecondCorinthiansComfortTribulationWitness
end Gnosis.Witnesses.Bible.SecondCorinthians
