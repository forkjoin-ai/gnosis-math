import Init

namespace Gnosis.Witnesses.Bible.SecondThessalonians
namespace SecondThessaloniansDisorderlyWorkPeaceWitness

/-!
# 2 Thessalonians 3:1-18 -- Free-Course Word, Disorderly Work, Brotherly Admonition

Source text: `docs/ebooks/source-texts/bible-kjv.txt:95224-95258`.

The closing discipline does not confuse peace with passivity. The word must run
freely; the community must withdraw from disorderly idleness; correction remains
brotherly rather than enemy-making.

No `sorry`, no new `axiom`.
-/

structure FreeCourseStability where
  prayWordFreeCourseGlorified : Bool := true
  deliveredFromWickedUnfaithful : Bool := true
  lordFaithfulEstablishesKeeps : Bool := true
  confidenceInObedience : Bool := true
  heartsDirectedLovePatience : Bool := true
deriving DecidableEq, Repr

def freeCourseStability : FreeCourseStability := {}

def freeCourseWitness (f : FreeCourseStability) : Prop :=
  f.prayWordFreeCourseGlorified = true ∧
  f.deliveredFromWickedUnfaithful = true ∧
  f.lordFaithfulEstablishesKeeps = true ∧
  f.confidenceInObedience = true ∧
  f.heartsDirectedLovePatience = true

structure DisorderlyWorkCorrection where
  withdrawFromDisorderly : Bool := true
  apostolicExampleNotDisorderly : Bool := true
  laboredNotChargeable : Bool := true
  ifNotWorkNotEat : Bool := true
  busybodyIdlenessNamed : Bool := true
  quietWorkOwnBread : Bool := true
  notWearyInWellDoing : Bool := true
  noteDisobedientNoCompany : Bool := true
  admonishAsBrotherNotEnemy : Bool := true
  peaceAlwaysByAllMeans : Bool := true
  ownHandTokenAndGrace : Bool := true
deriving DecidableEq, Repr

def disorderlyWorkCorrection : DisorderlyWorkCorrection := {}

def disorderlyWorkWitness (d : DisorderlyWorkCorrection) : Prop :=
  d.withdrawFromDisorderly = true ∧
  d.apostolicExampleNotDisorderly = true ∧
  d.laboredNotChargeable = true ∧
  d.ifNotWorkNotEat = true ∧
  d.busybodyIdlenessNamed = true ∧
  d.quietWorkOwnBread = true ∧
  d.notWearyInWellDoing = true ∧
  d.noteDisobedientNoCompany = true ∧
  d.admonishAsBrotherNotEnemy = true ∧
  d.peaceAlwaysByAllMeans = true ∧
  d.ownHandTokenAndGrace = true

theorem second_thessalonians_free_course :
    freeCourseWitness freeCourseStability := by
  unfold freeCourseWitness freeCourseStability
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem second_thessalonians_disorderly_work :
    disorderlyWorkWitness disorderlyWorkCorrection := by
  unfold disorderlyWorkWitness disorderlyWorkCorrection
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem second_thessalonians_disorderly_work_peace_witness :
    freeCourseWitness freeCourseStability ∧
    disorderlyWorkWitness disorderlyWorkCorrection := by
  exact ⟨second_thessalonians_free_course,
    second_thessalonians_disorderly_work⟩

end SecondThessaloniansDisorderlyWorkPeaceWitness
end Gnosis.Witnesses.Bible.SecondThessalonians
