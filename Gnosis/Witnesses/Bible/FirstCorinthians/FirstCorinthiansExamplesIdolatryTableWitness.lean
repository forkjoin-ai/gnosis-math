import Init

namespace Gnosis.Witnesses.Bible.FirstCorinthians
namespace FirstCorinthiansExamplesIdolatryTableWitness

/-! # 1 Corinthians 10 -- Examples, Temptation, Idolatry, and Table
Source text: `docs/ebooks/source-texts/bible-kjv.txt:92166-92248`. -/

structure ExamplesIdolatryTable where
  fathersCloudSeaRockChrist : Bool
  examplesAgainstLustIdolatryFornicationMurmuring : Bool
  temptationCommonGodFaithfulEscape : Bool
  fleeIdolatry : Bool
  cupAndBreadCommunion : Bool
  cannotDrinkLordCupAndDevilsCup : Bool
  allThingsNotExpedientEdify : Bool
  doAllToGloryOfGod : Bool
  pleaseAllThatTheyMayBeSaved : Bool
deriving DecidableEq, Repr

def examplesIdolatryTable : ExamplesIdolatryTable where
  fathersCloudSeaRockChrist := true
  examplesAgainstLustIdolatryFornicationMurmuring := true
  temptationCommonGodFaithfulEscape := true
  fleeIdolatry := true
  cupAndBreadCommunion := true
  cannotDrinkLordCupAndDevilsCup := true
  allThingsNotExpedientEdify := true
  doAllToGloryOfGod := true
  pleaseAllThatTheyMayBeSaved := true

theorem first_corinthians_examples_idolatry_table_witness :
    examplesIdolatryTable.fathersCloudSeaRockChrist = true
    ∧ examplesIdolatryTable.examplesAgainstLustIdolatryFornicationMurmuring = true
    ∧ examplesIdolatryTable.temptationCommonGodFaithfulEscape = true
    ∧ examplesIdolatryTable.fleeIdolatry = true
    ∧ examplesIdolatryTable.cupAndBreadCommunion = true
    ∧ examplesIdolatryTable.cannotDrinkLordCupAndDevilsCup = true
    ∧ examplesIdolatryTable.allThingsNotExpedientEdify = true
    ∧ examplesIdolatryTable.doAllToGloryOfGod = true
    ∧ examplesIdolatryTable.pleaseAllThatTheyMayBeSaved = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end FirstCorinthiansExamplesIdolatryTableWitness
end Gnosis.Witnesses.Bible.FirstCorinthians
