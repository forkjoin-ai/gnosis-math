import Gnosis.ArchaeologicalInfinityAccess
import Gnosis.TruthOneManyNamesWitness

namespace Gnosis.Witnesses.Islam
namespace QuranAlAsrSuraQualityWitness

/-! # Quran 103, Al-Asr / Time -- Complete Sura Quality Witness

Source anchor `/tmp/emotions-quran/abdel-haleem-quran.txt:16241-16255`.
Covers Quran 103:1-3: declining time, human loss, and the exception of faith,
good deeds, truth-counsel, and patience-counsel. -/

inductive AsrCluster | timeOath | loss | faithfulCounsel deriving DecidableEq, Repr
def asrClusters : List AsrCluster := [.timeOath, .loss, .faithfulCounsel]
structure AsrLedger where
  humansAreInLossWithoutException : Bool := true
  faithAndGoodDeedsOpenException : Bool := true
  truthAndPatienceMustBeMutuallyCounseled : Bool := true
deriving DecidableEq, Repr
def asrLedger : AsrLedger := {}
def asrSat (l : AsrLedger) : Prop :=
  l.humansAreInLossWithoutException = true ∧ l.faithAndGoodDeedsOpenException = true ∧
  l.truthAndPatienceMustBeMutuallyCounseled = true
structure AsrGap where
  timeCanBeSpentIntoLoss : Bool := true
  isolatedFaithMissesCounsel : Bool := true
  patienceCanBeSeparatedFromTruth : Bool := true
deriving DecidableEq, Repr
def asrGap : AsrGap := {}
def asrGaps (g : AsrGap) : Prop :=
  g.timeCanBeSpentIntoLoss = true ∧ g.isolatedFaithMissesCounsel = true ∧
  g.patienceCanBeSeparatedFromTruth = true
def asrAccess : Gnosis.ArchaeologicalInfinityAccess.Access :=
  { claim := "Quran 103 / Al-Asr witnesses time-loss and the faith/truth/patience exception"
    positiveSamples := [1, 2, 3], negativeSamples := [4, 5, 6] }
inductive AsrRegister | time | loss | truth | patience deriving DecidableEq, Repr, Nonempty
inductive AsrInvariant | counseledException deriving DecidableEq, Repr
def asrRegistersAgree :
    TruthOneManyNamesWitness.manyNamesAgree
      (fun _ : AsrRegister => AsrInvariant.counseledException)
      AsrInvariant.counseledException :=
  TruthOneManyNamesWitness.constant_names_agree AsrInvariant.counseledException
theorem quran_al_asr_sura_quality_witness :
    asrClusters.length = 3 ∧ asrSat asrLedger ∧ asrGaps asrGap ∧
    asrAccess.mode = Gnosis.ArchaeologicalInfinityAccess.AccessMode.archaeological ∧
    TruthOneManyNamesWitness.manyNamesAgree
      (fun _ : AsrRegister => AsrInvariant.counseledException)
      AsrInvariant.counseledException := by
  unfold asrSat asrLedger asrGaps asrGap
  exact ⟨rfl, ⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩, rfl, asrRegistersAgree⟩

end QuranAlAsrSuraQualityWitness
end Gnosis.Witnesses.Islam
