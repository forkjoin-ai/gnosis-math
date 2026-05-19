import Init

namespace Gnosis.Witnesses.Bible.FirstCorinthians
namespace FirstCorinthiansCarnalBuildersTempleWitness

/-! # 1 Corinthians 3 -- Carnal Divisions, Builders, and Temple
Source text: `docs/ebooks/source-texts/bible-kjv.txt:91721-91776`. -/

structure CarnalBuildersTemple where
  carnalMilkAndEnvy : Bool
  paulPlantsApollosWatersGodIncrease : Bool
  labourersTogetherWithGod : Bool
  foundationJesusChrist : Bool
  workTriedByFire : Bool
  templeOfGodSpiritDwells : Bool
  wisdomOfWorldFoolishness : Bool
  allThingsYoursYeChrists : Bool
deriving DecidableEq, Repr

def carnalBuildersTemple : CarnalBuildersTemple where
  carnalMilkAndEnvy := true
  paulPlantsApollosWatersGodIncrease := true
  labourersTogetherWithGod := true
  foundationJesusChrist := true
  workTriedByFire := true
  templeOfGodSpiritDwells := true
  wisdomOfWorldFoolishness := true
  allThingsYoursYeChrists := true

theorem first_corinthians_carnal_builders_temple_witness :
    carnalBuildersTemple.carnalMilkAndEnvy = true
    ∧ carnalBuildersTemple.paulPlantsApollosWatersGodIncrease = true
    ∧ carnalBuildersTemple.labourersTogetherWithGod = true
    ∧ carnalBuildersTemple.foundationJesusChrist = true
    ∧ carnalBuildersTemple.workTriedByFire = true
    ∧ carnalBuildersTemple.templeOfGodSpiritDwells = true
    ∧ carnalBuildersTemple.wisdomOfWorldFoolishness = true
    ∧ carnalBuildersTemple.allThingsYoursYeChrists = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end FirstCorinthiansCarnalBuildersTempleWitness
end Gnosis.Witnesses.Bible.FirstCorinthians
