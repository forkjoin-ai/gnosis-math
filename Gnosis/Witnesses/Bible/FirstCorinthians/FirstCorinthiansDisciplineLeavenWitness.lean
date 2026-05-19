import Init

namespace Gnosis.Witnesses.Bible.FirstCorinthians
namespace FirstCorinthiansDisciplineLeavenWitness

/-! # 1 Corinthians 5 -- Discipline, Leaven, and Judging Within
Source text: `docs/ebooks/source-texts/bible-kjv.txt:91841-91874`. -/

structure DisciplineLeaven where
  reportedFornicationAndPuffedUp : Bool
  deliverForDestructionThatSpiritSaved : Bool
  littleLeavenLeavensLump : Bool
  christPassoverSacrificed : Bool
  feastWithSincerityTruth : Bool
  notCompanyWithCalledBrotherWickedness : Bool
  judgeThemWithin : Bool
  putAwayWickedPerson : Bool
deriving DecidableEq, Repr

def disciplineLeaven : DisciplineLeaven where
  reportedFornicationAndPuffedUp := true
  deliverForDestructionThatSpiritSaved := true
  littleLeavenLeavensLump := true
  christPassoverSacrificed := true
  feastWithSincerityTruth := true
  notCompanyWithCalledBrotherWickedness := true
  judgeThemWithin := true
  putAwayWickedPerson := true

theorem first_corinthians_discipline_leaven_witness :
    disciplineLeaven.reportedFornicationAndPuffedUp = true
    ∧ disciplineLeaven.deliverForDestructionThatSpiritSaved = true
    ∧ disciplineLeaven.littleLeavenLeavensLump = true
    ∧ disciplineLeaven.christPassoverSacrificed = true
    ∧ disciplineLeaven.feastWithSincerityTruth = true
    ∧ disciplineLeaven.notCompanyWithCalledBrotherWickedness = true
    ∧ disciplineLeaven.judgeThemWithin = true
    ∧ disciplineLeaven.putAwayWickedPerson = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end FirstCorinthiansDisciplineLeavenWitness
end Gnosis.Witnesses.Bible.FirstCorinthians
