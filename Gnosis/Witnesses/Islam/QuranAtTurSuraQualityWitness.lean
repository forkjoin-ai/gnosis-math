import Gnosis.ArchaeologicalInfinityAccess
import Gnosis.TruthOneManyNamesWitness

namespace Gnosis.Witnesses.Islam
namespace QuranAtTurSuraQualityWitness

/-!
# Quran 52, At-Tur / The Mountain -- Complete Sura Quality Witness

Source text: `docs/ebooks/source-texts/abdel-haleem-quran.pdf`, extracted with
`pdftotext -layout`; text anchor `/tmp/emotions-quran/abdel-haleem-quran.txt:13687-13724`.

This complete sura witness covers Quran 52:1-49.

At-Tur is the inscribed-oath-and-watchfulness witness. Mountain, inscribed
Scripture, visited House, raised canopy, and swelling sea swear to unavoidable
judgment; deniers are pushed into Fire; the mindful receive family reunion and
provision; accusations of poet, madness, fabrication, or debt collapse; and the
Prophet is told to wait, praise, and watch under God's judgment.

No `sorry`, no new `axiom`.
-/

inductive TurQualityCluster
  | mountainInscribedBookHouseCanopyAndSeaOaths
  | unavoidableJudgmentAndFireExposure
  | mindfulGardensFamilyReunionAndProvision
  | accusationCollapseAndCreationQuestions
  | waitingPraiseAndDivineWatch
deriving DecidableEq, Repr

def turQualityClusters : List TurQualityCluster :=
  [ .mountainInscribedBookHouseCanopyAndSeaOaths
  , .unavoidableJudgmentAndFireExposure
  , .mindfulGardensFamilyReunionAndProvision
  , .accusationCollapseAndCreationQuestions
  , .waitingPraiseAndDivineWatch
  ]

structure TurInvariantLedger where
  oathLedgerMakesJudgmentUnavoidable : Bool := true
  mindfulFamiliesCanBeJoinedByFaith : Bool := true
  provisionAnswersPatientReceptivity : Bool := true
  creationQuestionsExposeGroundlessDenial : Bool := true
  praiseSustainsWaitingUnderDivineWatch : Bool := true
deriving DecidableEq, Repr

def turInvariantLedger : TurInvariantLedger := {}

def turSat (l : TurInvariantLedger) : Prop :=
  l.oathLedgerMakesJudgmentUnavoidable = true ∧
  l.mindfulFamiliesCanBeJoinedByFaith = true ∧
  l.provisionAnswersPatientReceptivity = true ∧
  l.creationQuestionsExposeGroundlessDenial = true ∧
  l.praiseSustainsWaitingUnderDivineWatch = true

structure TurGapLedger where
  denialTreatsJudgmentAsPlay : Bool := true
  revelationIsCalledPoetryOrFabrication : Bool := true
  debtAndControlClaimsMaskRefusal : Bool := true
  fallingSkyWouldStillBeCalledClouds : Bool := true
  plottingReturnsAgainstPlotters : Bool := true
deriving DecidableEq, Repr

def turGapLedger : TurGapLedger := {}

def turGapsExposeBoundary (g : TurGapLedger) : Prop :=
  g.denialTreatsJudgmentAsPlay = true ∧
  g.revelationIsCalledPoetryOrFabrication = true ∧
  g.debtAndControlClaimsMaskRefusal = true ∧
  g.fallingSkyWouldStillBeCalledClouds = true ∧
  g.plottingReturnsAgainstPlotters = true

def turSuraAccess : Gnosis.ArchaeologicalInfinityAccess.Access :=
  { claim := "Quran 52 / At-Tur witnesses inscribed oaths, family repair, and watchful praise"
    positiveSamples := [1, 2, 3, 4, 5]
    negativeSamples := [6, 7, 8, 9, 10] }

inductive TurRegister | mountain | book | house | sea | family | praise
deriving DecidableEq, Repr, Nonempty

inductive TurInvariant | inscribedOathWatch
deriving DecidableEq, Repr

def turRegistersAgree :
    TruthOneManyNamesWitness.manyNamesAgree
      (fun _ : TurRegister => TurInvariant.inscribedOathWatch)
      TurInvariant.inscribedOathWatch :=
  TruthOneManyNamesWitness.constant_names_agree TurInvariant.inscribedOathWatch

theorem tur_quality_clusters_shape :
    turQualityClusters.length = 5 ∧
    turQualityClusters.head? = some .mountainInscribedBookHouseCanopyAndSeaOaths ∧
    turQualityClusters.getLast? = some .waitingPraiseAndDivineWatch := by
  exact ⟨rfl, rfl, rfl⟩

theorem tur_sat_witness : turSat turInvariantLedger := by
  unfold turSat turInvariantLedger
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem tur_gap_witness : turGapsExposeBoundary turGapLedger := by
  unfold turGapsExposeBoundary turGapLedger
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem tur_access_archaeological :
    turSuraAccess.mode =
      Gnosis.ArchaeologicalInfinityAccess.AccessMode.archaeological := by
  rfl

theorem quran_at_tur_sura_quality_witness :
    turQualityClusters.length = 5 ∧
    turSat turInvariantLedger ∧
    turGapsExposeBoundary turGapLedger ∧
    turSuraAccess.mode =
      Gnosis.ArchaeologicalInfinityAccess.AccessMode.archaeological ∧
    TruthOneManyNamesWitness.manyNamesAgree
      (fun _ : TurRegister => TurInvariant.inscribedOathWatch)
      TurInvariant.inscribedOathWatch := by
  exact ⟨tur_quality_clusters_shape.left, tur_sat_witness, tur_gap_witness,
    tur_access_archaeological, turRegistersAgree⟩

end QuranAtTurSuraQualityWitness
end Gnosis.Witnesses.Islam
