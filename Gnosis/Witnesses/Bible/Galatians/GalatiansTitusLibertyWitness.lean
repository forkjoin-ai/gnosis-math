import Init

namespace Gnosis.Witnesses.Bible.Galatians
namespace GalatiansTitusLibertyWitness

/-!
# Galatians 2:1-5 -- Titus, False Brethren, and Gospel Liberty

Source text: `docs/ebooks/source-texts/bible-kjv.txt:93634-93646`.

Paul goes up by revelation, communicates the Gentile gospel, and refuses the
false-brethren capture attempt: Titus, a Greek, is not compelled to be
circumcised, so the truth of the gospel continues.

No `sorry`, no new `axiom`.
-/

structure RevelationConference where
  wentUpByRevelation : Bool := true
  barnabasAndTitusIncluded : Bool := true
  gentileGospelCommunicated : Bool := true
  privateConferenceWithReputation : Bool := true
  vainRunningBoundaryNamed : Bool := true
deriving DecidableEq, Repr

def revelationConference : RevelationConference := {}

def revelationConferencePreservesGospel (r : RevelationConference) : Prop :=
  r.wentUpByRevelation = true ∧
  r.barnabasAndTitusIncluded = true ∧
  r.gentileGospelCommunicated = true ∧
  r.privateConferenceWithReputation = true ∧
  r.vainRunningBoundaryNamed = true

structure TitusLibertyBoundary where
  titusGreekNamed : Bool := true
  circumcisionNotCompelled : Bool := true
  falseBrethrenBroughtInUnawares : Bool := true
  libertySpiedOut : Bool := true
  bondageAttemptNamed : Bool := true
  noSubjectionForAnHour : Bool := true
  gospelTruthContinues : Bool := true
deriving DecidableEq, Repr

def titusLibertyBoundary : TitusLibertyBoundary := {}

def falseBrethrenCaptureFails (b : TitusLibertyBoundary) : Prop :=
  b.titusGreekNamed = true ∧
  b.circumcisionNotCompelled = true ∧
  b.falseBrethrenBroughtInUnawares = true ∧
  b.libertySpiedOut = true ∧
  b.bondageAttemptNamed = true ∧
  b.noSubjectionForAnHour = true ∧
  b.gospelTruthContinues = true

theorem galatians_revelation_conference :
    revelationConferencePreservesGospel revelationConference := by
  unfold revelationConferencePreservesGospel revelationConference
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem galatians_titus_liberty_boundary :
    falseBrethrenCaptureFails titusLibertyBoundary := by
  unfold falseBrethrenCaptureFails titusLibertyBoundary
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem galatians_titus_liberty_witness :
    revelationConferencePreservesGospel revelationConference ∧
    falseBrethrenCaptureFails titusLibertyBoundary := by
  exact ⟨galatians_revelation_conference, galatians_titus_liberty_boundary⟩

end GalatiansTitusLibertyWitness
end Gnosis.Witnesses.Bible.Galatians
