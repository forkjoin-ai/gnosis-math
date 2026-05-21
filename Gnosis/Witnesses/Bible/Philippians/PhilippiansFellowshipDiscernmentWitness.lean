import Init

namespace Gnosis.Witnesses.Bible.Philippians
namespace PhilippiansFellowshipDiscernmentWitness

/-!
# Philippians 1:1-11 -- Gospel Fellowship and Discernment Love

Source text: `docs/ebooks/source-texts/bible-kjv.txt:94354-94383`.

The opening binds fellowship, bonds, defense, and discernment. Love is not left
as a generic affect; it is asked to abound in knowledge and judgment so excellent
things can be approved.

No `sorry`, no new `axiom`.
-/

structure FellowshipDiscernment where
  servantsAddressSaints : Bool := true
  gospelFellowshipFromFirstDay : Bool := true
  goodWorkPerformedUntilDay : Bool := true
  bondsDefenseConfirmationShared : Bool := true
  longingInChristNamed : Bool := true
  loveAboundsInKnowledgeJudgment : Bool := true
  excellentThingsApproved : Bool := true
  fruitsOfRighteousnessFilled : Bool := true
deriving DecidableEq, Repr

def fellowshipDiscernment : FellowshipDiscernment := {}

def fellowshipDiscernmentWitness (f : FellowshipDiscernment) : Prop :=
  f.servantsAddressSaints = true ∧ f.gospelFellowshipFromFirstDay = true ∧
  f.goodWorkPerformedUntilDay = true ∧ f.bondsDefenseConfirmationShared = true ∧
  f.longingInChristNamed = true ∧ f.loveAboundsInKnowledgeJudgment = true ∧
  f.excellentThingsApproved = true ∧ f.fruitsOfRighteousnessFilled = true

theorem philippians_fellowship_discernment :
    fellowshipDiscernmentWitness fellowshipDiscernment := by
  unfold fellowshipDiscernmentWitness fellowshipDiscernment
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end PhilippiansFellowshipDiscernmentWitness
end Gnosis.Witnesses.Bible.Philippians
