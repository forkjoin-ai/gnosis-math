import Init

namespace Gnosis.Witnesses.Bible.FirstTimothy
namespace FirstTimothyGodlinessDisciplineWitness

/-!
# 1 Timothy 4 -- False Asceticism, Godliness Exercise, and Doctrine Attendance

Source text: `docs/ebooks/source-texts/bible-kjv.txt:95413-95464`.

The departure gap is ascetic counterfeit: forbidding what God created for
thanksgiving while conscience is seared. The positive discipline is godliness,
reading, exhortation, doctrine, gift-attention, and self/doctrine continuance.

No `sorry`, no new `axiom`.
-/

structure AsceticCounterfeit where
  latterDepartureFromFaith : Bool := true
  seducingSpiritsDoctrinesDevils : Bool := true
  liesHypocrisySearedConscience : Bool := true
  marriageAndMeatsForbidden : Bool := true
  creaturesReceivedWithThanksgiving : Bool := true
  sanctifiedByWordPrayer : Bool := true
deriving DecidableEq, Repr

def asceticCounterfeit : AsceticCounterfeit := {}

def asceticCounterfeitWitness (a : AsceticCounterfeit) : Prop :=
  a.latterDepartureFromFaith = true ∧ a.seducingSpiritsDoctrinesDevils = true ∧
  a.liesHypocrisySearedConscience = true ∧ a.marriageAndMeatsForbidden = true ∧
  a.creaturesReceivedWithThanksgiving = true ∧ a.sanctifiedByWordPrayer = true

structure GodlinessDiscipline where
  goodMinisterRemembrance : Bool := true
  nourishedInFaithGoodDoctrine : Bool := true
  fablesRefused : Bool := true
  exerciseUntoGodliness : Bool := true
  godlinessProfitableAllThings : Bool := true
  youthExampleInWordConductLove : Bool := true
  attendanceReadingExhortationDoctrine : Bool := true
  giftNotNeglected : Bool := true
  selfAndDoctrineContinued : Bool := true
deriving DecidableEq, Repr

def godlinessDiscipline : GodlinessDiscipline := {}

def godlinessDisciplineWitness (g : GodlinessDiscipline) : Prop :=
  g.goodMinisterRemembrance = true ∧ g.nourishedInFaithGoodDoctrine = true ∧
  g.fablesRefused = true ∧ g.exerciseUntoGodliness = true ∧
  g.godlinessProfitableAllThings = true ∧ g.youthExampleInWordConductLove = true ∧
  g.attendanceReadingExhortationDoctrine = true ∧ g.giftNotNeglected = true ∧
  g.selfAndDoctrineContinued = true

theorem first_timothy_ascetic_counterfeit :
    asceticCounterfeitWitness asceticCounterfeit := by
  unfold asceticCounterfeitWitness asceticCounterfeit
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem first_timothy_godliness_discipline :
    godlinessDisciplineWitness godlinessDiscipline := by
  unfold godlinessDisciplineWitness godlinessDiscipline
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem first_timothy_godliness_discipline_witness :
    asceticCounterfeitWitness asceticCounterfeit ∧
    godlinessDisciplineWitness godlinessDiscipline := by
  exact ⟨first_timothy_ascetic_counterfeit,
    first_timothy_godliness_discipline⟩

end FirstTimothyGodlinessDisciplineWitness
end Gnosis.Witnesses.Bible.FirstTimothy
