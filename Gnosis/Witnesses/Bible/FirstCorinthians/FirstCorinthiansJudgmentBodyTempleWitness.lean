import Init

namespace Gnosis.Witnesses.Bible.FirstCorinthians
namespace FirstCorinthiansJudgmentBodyTempleWitness

/-! # 1 Corinthians 6 -- Judgment, Body, and Temple
Source text: `docs/ebooks/source-texts/bible-kjv.txt:91876-91930`. -/

structure JudgmentBodyTemple where
  mattersBeforeSaintsNotUnjust : Bool
  saintsJudgeWorldAndAngels : Bool
  wrongSufferedRatherThanDefrauding : Bool
  unrighteousNotInheritKingdom : Bool
  washedSanctifiedJustified : Bool
  bodyForLord : Bool
  membersOfChristNotHarlot : Bool
  bodyTempleHolyGhost : Bool
  boughtWithPriceGlorifyGod : Bool
deriving DecidableEq, Repr

def judgmentBodyTemple : JudgmentBodyTemple where
  mattersBeforeSaintsNotUnjust := true
  saintsJudgeWorldAndAngels := true
  wrongSufferedRatherThanDefrauding := true
  unrighteousNotInheritKingdom := true
  washedSanctifiedJustified := true
  bodyForLord := true
  membersOfChristNotHarlot := true
  bodyTempleHolyGhost := true
  boughtWithPriceGlorifyGod := true

theorem first_corinthians_judgment_body_temple_witness :
    judgmentBodyTemple.mattersBeforeSaintsNotUnjust = true
    ∧ judgmentBodyTemple.saintsJudgeWorldAndAngels = true
    ∧ judgmentBodyTemple.wrongSufferedRatherThanDefrauding = true
    ∧ judgmentBodyTemple.unrighteousNotInheritKingdom = true
    ∧ judgmentBodyTemple.washedSanctifiedJustified = true
    ∧ judgmentBodyTemple.bodyForLord = true
    ∧ judgmentBodyTemple.membersOfChristNotHarlot = true
    ∧ judgmentBodyTemple.bodyTempleHolyGhost = true
    ∧ judgmentBodyTemple.boughtWithPriceGlorifyGod = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end FirstCorinthiansJudgmentBodyTempleWitness
end Gnosis.Witnesses.Bible.FirstCorinthians
