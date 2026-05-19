import Init

namespace Gnosis.Witnesses.Bible.SecondCorinthians
namespace SecondCorinthiansWarfareMeasureWitness

/-! # 2 Corinthians 10 -- Warfare, Measure, and Lord's Commendation
Source text: `docs/ebooks/source-texts/bible-kjv.txt:93303-93354`. -/

structure WarfareMeasure where
  meeknessGentlenessChrist : Bool
  walkFleshNotWarAfterFlesh : Bool
  weaponsNotCarnalMightyThroughGod : Bool
  thoughtsCaptiveObedienceChrist : Bool
  authorityForEdificationNotDestruction : Bool
  lettersAndPresenceAnswer : Bool
  notMeasureBySelfComparison : Bool
  measureRuleDistributedByGod : Bool
  preachRegionsBeyondNotOtherLine : Bool
  gloryInLordLordCommends : Bool
deriving DecidableEq, Repr

def warfareMeasure : WarfareMeasure where
  meeknessGentlenessChrist := true
  walkFleshNotWarAfterFlesh := true
  weaponsNotCarnalMightyThroughGod := true
  thoughtsCaptiveObedienceChrist := true
  authorityForEdificationNotDestruction := true
  lettersAndPresenceAnswer := true
  notMeasureBySelfComparison := true
  measureRuleDistributedByGod := true
  preachRegionsBeyondNotOtherLine := true
  gloryInLordLordCommends := true

theorem second_corinthians_warfare_measure_witness :
    warfareMeasure.meeknessGentlenessChrist = true
    ∧ warfareMeasure.walkFleshNotWarAfterFlesh = true
    ∧ warfareMeasure.weaponsNotCarnalMightyThroughGod = true
    ∧ warfareMeasure.thoughtsCaptiveObedienceChrist = true
    ∧ warfareMeasure.authorityForEdificationNotDestruction = true
    ∧ warfareMeasure.lettersAndPresenceAnswer = true
    ∧ warfareMeasure.notMeasureBySelfComparison = true
    ∧ warfareMeasure.measureRuleDistributedByGod = true
    ∧ warfareMeasure.preachRegionsBeyondNotOtherLine = true
    ∧ warfareMeasure.gloryInLordLordCommends = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end SecondCorinthiansWarfareMeasureWitness
end Gnosis.Witnesses.Bible.SecondCorinthians
