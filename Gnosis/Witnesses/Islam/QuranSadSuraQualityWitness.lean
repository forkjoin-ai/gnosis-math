import Gnosis.ArchaeologicalInfinityAccess
import Gnosis.TruthOneManyNamesWitness

namespace Gnosis.Witnesses.Islam
namespace QuranSadSuraQualityWitness

/-!
# Quran 38, Sad -- Complete Sura Quality Witness

Source text: `docs/ebooks/source-texts/abdel-haleem-quran.pdf`, extracted with
`pdftotext -layout`; text anchor `/tmp/emotions-quran/abdel-haleem-quran.txt:11816-11968`.

This complete sura witness covers Quran 38:1-88.

Sad is the judgment-and-pride counterproof. The Quran as reminder, arrogant
hostility to one God, David's judgment test, fair ruling, purposeful creation,
blessed Scripture, Solomon's horses, wind, and jinn, Job's suffering and patient
restoration, remembered servants, Heaven and Hell dispute, the single Lord,
Adam's formation, Iblis's fire-over-clay pride, respite, and the protected
servants boundary all turn pride into the exposed gap of judgment.

No `sorry`, no new `axiom`.
-/

inductive SadQualityCluster
  | reminderArroganceAndOneGodObjection
  | davidJudgmentTestAndPurposefulCreation
  | solomonHorsesWindJinnAndReturn
  | jobPatienceRememberedServantsAndAfterlifeDispute
  | adamIblisPrideRespiteAndProtectedServants
deriving DecidableEq, Repr

def sadQualityClusters : List SadQualityCluster :=
  [ SadQualityCluster.reminderArroganceAndOneGodObjection
  , SadQualityCluster.davidJudgmentTestAndPurposefulCreation
  , SadQualityCluster.solomonHorsesWindJinnAndReturn
  , SadQualityCluster.jobPatienceRememberedServantsAndAfterlifeDispute
  , SadQualityCluster.adamIblisPrideRespiteAndProtectedServants
  ]

structure SadInvariantLedger where
  reminderConfrontsPride : Bool := true
  judgmentRequiresFairnessOverDesire : Bool := true
  creationHasPurposeAgainstEmptyEquivalence : Bool := true
  patientReturnRestoresServanthood : Bool := true
  oneLordFramesAllWarning : Bool := true
  protectedServantsEscapeIblisClaim : Bool := true
deriving DecidableEq, Repr

def sadInvariantLedger : SadInvariantLedger := {}

def sadSat (l : SadInvariantLedger) : Prop :=
  l.reminderConfrontsPride = true ∧
  l.judgmentRequiresFairnessOverDesire = true ∧
  l.creationHasPurposeAgainstEmptyEquivalence = true ∧
  l.patientReturnRestoresServanthood = true ∧
  l.oneLordFramesAllWarning = true ∧
  l.protectedServantsEscapeIblisClaim = true

structure SadGapLedger where
  arroganceRejectsOneGod : Bool := true
  litigantsExposeJudgmentTemptation : Bool := true
  desireCanMisleadRuling : Bool := true
  hellPartiesBlameEachOther : Bool := true
  iblisRefusesClayThroughFirePride : Bool := true
  warningCanBeDismissedUntilKnownLater : Bool := true
deriving DecidableEq, Repr

def sadGapLedger : SadGapLedger := {}

def sadGapsExposeBoundary (g : SadGapLedger) : Prop :=
  g.arroganceRejectsOneGod = true ∧
  g.litigantsExposeJudgmentTemptation = true ∧
  g.desireCanMisleadRuling = true ∧
  g.hellPartiesBlameEachOther = true ∧
  g.iblisRefusesClayThroughFirePride = true ∧
  g.warningCanBeDismissedUntilKnownLater = true

def sadSuraAccess : Gnosis.ArchaeologicalInfinityAccess.Access :=
  { claim := "Quran 38 / Sad witnesses fair judgment, purposeful creation, patience, and pride's failure"
    positiveSamples := [1, 2, 3, 4, 5, 6]
    negativeSamples := [7, 8, 9, 10, 11, 12] }

inductive SadRegister | reminder | david | creation | solomon | job | adam | warning
deriving DecidableEq, Repr, Nonempty

inductive SadInvariant | judgmentAgainstPride
deriving DecidableEq, Repr

def sadRegistersAgree :
    TruthOneManyNamesWitness.manyNamesAgree
      (fun _ : SadRegister => SadInvariant.judgmentAgainstPride)
      SadInvariant.judgmentAgainstPride :=
  TruthOneManyNamesWitness.constant_names_agree SadInvariant.judgmentAgainstPride

theorem sad_quality_clusters_shape :
    sadQualityClusters.length = 5
    ∧ sadQualityClusters.head? =
      some SadQualityCluster.reminderArroganceAndOneGodObjection
    ∧ sadQualityClusters.getLast? =
      some SadQualityCluster.adamIblisPrideRespiteAndProtectedServants := by
  exact ⟨rfl, rfl, rfl⟩

theorem sad_sat_witness : sadSat sadInvariantLedger := by
  unfold sadSat sadInvariantLedger
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem sad_gap_witness : sadGapsExposeBoundary sadGapLedger := by
  unfold sadGapsExposeBoundary sadGapLedger
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem sad_access_archaeological :
    sadSuraAccess.mode =
      Gnosis.ArchaeologicalInfinityAccess.AccessMode.archaeological := by
  rfl

theorem quran_sad_sura_quality_witness :
    sadQualityClusters.length = 5 ∧
    sadSat sadInvariantLedger ∧
    sadGapsExposeBoundary sadGapLedger ∧
    sadSuraAccess.mode =
      Gnosis.ArchaeologicalInfinityAccess.AccessMode.archaeological ∧
    TruthOneManyNamesWitness.manyNamesAgree
      (fun _ : SadRegister => SadInvariant.judgmentAgainstPride)
      SadInvariant.judgmentAgainstPride := by
  exact ⟨sad_quality_clusters_shape.left, sad_sat_witness, sad_gap_witness,
    sad_access_archaeological, sadRegistersAgree⟩

end QuranSadSuraQualityWitness
end Gnosis.Witnesses.Islam
