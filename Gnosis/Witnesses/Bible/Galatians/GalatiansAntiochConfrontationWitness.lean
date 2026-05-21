import Init

namespace Gnosis.Witnesses.Bible.Galatians
namespace GalatiansAntiochConfrontationWitness

/-!
# Galatians 2:11-16 -- Antioch Confrontation and Justification Boundary

Source text: `docs/ebooks/source-texts/bible-kjv.txt:93663-93685`.

Peter's table withdrawal is treated as a public truth-boundary failure. Fear of
the circumcision creates dissimulation; Paul names the incoherence and restates
the justification boundary: not works of law, but faith of Jesus Christ.

No `sorry`, no new `axiom`.
-/

structure AntiochWithdrawal where
  peterWithstoodToFace : Bool := true
  peterBlameworthy : Bool := true
  ateWithGentilesBeforeCertainCame : Bool := true
  withdrewAndSeparatedFromFear : Bool := true
  jewsDissembledLikewise : Bool := true
  barnabasCarriedAway : Bool := true
deriving DecidableEq, Repr

def antiochWithdrawal : AntiochWithdrawal := {}

def tableWithdrawalExposesFearGap (w : AntiochWithdrawal) : Prop :=
  w.peterWithstoodToFace = true ∧
  w.peterBlameworthy = true ∧
  w.ateWithGentilesBeforeCertainCame = true ∧
  w.withdrewAndSeparatedFromFear = true ∧
  w.jewsDissembledLikewise = true ∧
  w.barnabasCarriedAway = true

structure GospelUprightness where
  walkedNotUprightly : Bool := true
  truthOfGospelNamed : Bool := true
  publicCorrectionGiven : Bool := true
  jewishGentilePracticeIncoherenceNamed : Bool := true
deriving DecidableEq, Repr

def gospelUprightness : GospelUprightness := {}

def publicCorrectionRestoresBoundary (g : GospelUprightness) : Prop :=
  g.walkedNotUprightly = true ∧
  g.truthOfGospelNamed = true ∧
  g.publicCorrectionGiven = true ∧
  g.jewishGentilePracticeIncoherenceNamed = true

structure JustificationBoundary where
  notJustifiedByWorksOfLaw : Bool := true
  justifiedByFaithOfJesusChrist : Bool := true
  believedInJesusChrist : Bool := true
  noFleshJustifiedByWorksOfLaw : Bool := true
deriving DecidableEq, Repr

def justificationBoundary : JustificationBoundary := {}

def faithNotLawJustifies (j : JustificationBoundary) : Prop :=
  j.notJustifiedByWorksOfLaw = true ∧
  j.justifiedByFaithOfJesusChrist = true ∧
  j.believedInJesusChrist = true ∧
  j.noFleshJustifiedByWorksOfLaw = true

theorem galatians_table_withdrawal_gap :
    tableWithdrawalExposesFearGap antiochWithdrawal := by
  unfold tableWithdrawalExposesFearGap antiochWithdrawal
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem galatians_public_correction :
    publicCorrectionRestoresBoundary gospelUprightness := by
  unfold publicCorrectionRestoresBoundary gospelUprightness
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem galatians_justification_boundary :
    faithNotLawJustifies justificationBoundary := by
  unfold faithNotLawJustifies justificationBoundary
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem galatians_antioch_confrontation_witness :
    tableWithdrawalExposesFearGap antiochWithdrawal ∧
    publicCorrectionRestoresBoundary gospelUprightness ∧
    faithNotLawJustifies justificationBoundary := by
  exact ⟨galatians_table_withdrawal_gap,
    galatians_public_correction,
    galatians_justification_boundary⟩

end GalatiansAntiochConfrontationWitness
end Gnosis.Witnesses.Bible.Galatians
