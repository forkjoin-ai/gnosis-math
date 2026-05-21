import Init

namespace Gnosis.Witnesses.Bible.Galatians
namespace GalatiansSpiritFaithFleshWitness

/-!
# Galatians 3:1-5 -- Spirit Hearing Versus Flesh Completion

Source text: `docs/ebooks/source-texts/bible-kjv.txt:93700-93719`.

Paul treats the regression from Spirit to flesh as a capture gap. The witness is
not merely descriptive: it marks a failed completion strategy, where an already
opened Spirit runtime is incorrectly routed back through works of law.

No `sorry`, no new `axiom`.
-/

structure BewitchedRegression where
  truthObedienceInterrupted : Bool := true
  crucifiedChristSetForth : Bool := true
  spiritReceivedByHearingFaith : Bool := true
  worksOfLawRejectedAsSpiritSource : Bool := true
  begunInSpirit : Bool := true
  fleshCompletionRejected : Bool := true
deriving DecidableEq, Repr

def bewitchedRegression : BewitchedRegression := {}

def fleshCompletionGap (r : BewitchedRegression) : Prop :=
  r.truthObedienceInterrupted = true ∧
  r.crucifiedChristSetForth = true ∧
  r.spiritReceivedByHearingFaith = true ∧
  r.worksOfLawRejectedAsSpiritSource = true ∧
  r.begunInSpirit = true ∧
  r.fleshCompletionRejected = true

structure SpiritMinistration where
  ministeringSpiritNamed : Bool := true
  miraclesWorkedAmongYou : Bool := true
  notByWorksOfLaw : Bool := true
  byHearingOfFaith : Bool := true
deriving DecidableEq, Repr

def spiritMinistration : SpiritMinistration := {}

def spiritMinistrationByFaith (m : SpiritMinistration) : Prop :=
  m.ministeringSpiritNamed = true ∧
  m.miraclesWorkedAmongYou = true ∧
  m.notByWorksOfLaw = true ∧
  m.byHearingOfFaith = true

theorem galatians_flesh_completion_gap :
    fleshCompletionGap bewitchedRegression := by
  unfold fleshCompletionGap bewitchedRegression
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem galatians_spirit_ministration_by_faith :
    spiritMinistrationByFaith spiritMinistration := by
  unfold spiritMinistrationByFaith spiritMinistration
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem galatians_spirit_faith_flesh_witness :
    fleshCompletionGap bewitchedRegression ∧
    spiritMinistrationByFaith spiritMinistration := by
  exact ⟨galatians_flesh_completion_gap,
    galatians_spirit_ministration_by_faith⟩

end GalatiansSpiritFaithFleshWitness
end Gnosis.Witnesses.Bible.Galatians
