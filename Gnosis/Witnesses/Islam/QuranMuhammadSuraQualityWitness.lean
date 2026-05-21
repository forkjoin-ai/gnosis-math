import Gnosis.ArchaeologicalInfinityAccess
import Gnosis.TruthOneManyNamesWitness

namespace Gnosis.Witnesses.Islam
namespace QuranMuhammadSuraQualityWitness

/-!
# Quran 47, Muhammad -- Complete Sura Quality Witness

Source text: `docs/ebooks/source-texts/abdel-haleem-quran.pdf`, extracted with
`pdftotext -layout`; text anchor `/tmp/emotions-quran/abdel-haleem-quran.txt:13218-13294`.

This complete sura witness covers Quran 47:1-38.

Muhammad is the deed-nullification-and-testing witness: those who bar from
God's path have deeds brought to nothing, those who believe the truth sent down
to Muhammad are repaired, battle tests truthfulness, Paradise is described as
rivers, hypocrites expose diseased hearts, obedience is demanded, kinship ties
must not be severed, and miserly refusal only harms the refuser.

No `sorry`, no new `axiom`.
-/

inductive MuhammadQualityCluster
  | barredPathDeedsNullifiedAndBelieverRepair
  | battleTestCaptivesAndDivineHelp
  | paradiseRiversAndFireContrast
  | hypocriteDiseaseObedienceAndExposedHearts
  | kinshipTiesMiserlinessAndReplacementWarning
deriving DecidableEq, Repr

def muhammadQualityClusters : List MuhammadQualityCluster :=
  [ .barredPathDeedsNullifiedAndBelieverRepair
  , .battleTestCaptivesAndDivineHelp
  , .paradiseRiversAndFireContrast
  , .hypocriteDiseaseObedienceAndExposedHearts
  , .kinshipTiesMiserlinessAndReplacementWarning
  ]

structure MuhammadInvariantLedger where
  truthSentDownRepairsBelievers : Bool := true
  testingSeparatesTruthfulEndurance : Bool := true
  obedienceProtectsDeedsFromNullification : Bool := true
  heartsCanBeExposedByCommand : Bool := true
  generosityProtectsAgainstReplacement : Bool := true
deriving DecidableEq, Repr

def muhammadInvariantLedger : MuhammadInvariantLedger := {}

def muhammadSat (l : MuhammadInvariantLedger) : Prop :=
  l.truthSentDownRepairsBelievers = true ∧
  l.testingSeparatesTruthfulEndurance = true ∧
  l.obedienceProtectsDeedsFromNullification = true ∧
  l.heartsCanBeExposedByCommand = true ∧
  l.generosityProtectsAgainstReplacement = true

structure MuhammadGapLedger where
  barringGodsPathNullifiesDeeds : Bool := true
  hypocriteDiseaseWaitsForCommand : Bool := true
  severedKinshipSignalsCorruption : Bool := true
  askingForgivenessIsRefusedByPride : Bool := true
  miserlinessHarmsOnlyTheMiser : Bool := true
deriving DecidableEq, Repr

def muhammadGapLedger : MuhammadGapLedger := {}

def muhammadGapsExposeBoundary (g : MuhammadGapLedger) : Prop :=
  g.barringGodsPathNullifiesDeeds = true ∧
  g.hypocriteDiseaseWaitsForCommand = true ∧
  g.severedKinshipSignalsCorruption = true ∧
  g.askingForgivenessIsRefusedByPride = true ∧
  g.miserlinessHarmsOnlyTheMiser = true

def muhammadSuraAccess : Gnosis.ArchaeologicalInfinityAccess.Access :=
  { claim := "Quran 47 / Muhammad witnesses repaired truth, deed nullification, and tested hearts"
    positiveSamples := [1, 2, 3, 4, 5]
    negativeSamples := [6, 7, 8, 9, 10] }

inductive MuhammadRegister | truth | battle | paradise | hearts | kinship | giving
deriving DecidableEq, Repr, Nonempty

inductive MuhammadInvariant | truthRepairAgainstNullification
deriving DecidableEq, Repr

def muhammadRegistersAgree :
    TruthOneManyNamesWitness.manyNamesAgree
      (fun _ : MuhammadRegister => MuhammadInvariant.truthRepairAgainstNullification)
      MuhammadInvariant.truthRepairAgainstNullification :=
  TruthOneManyNamesWitness.constant_names_agree MuhammadInvariant.truthRepairAgainstNullification

theorem muhammad_quality_clusters_shape :
    muhammadQualityClusters.length = 5 ∧
    muhammadQualityClusters.head? = some .barredPathDeedsNullifiedAndBelieverRepair ∧
    muhammadQualityClusters.getLast? = some .kinshipTiesMiserlinessAndReplacementWarning := by
  exact ⟨rfl, rfl, rfl⟩

theorem muhammad_sat_witness : muhammadSat muhammadInvariantLedger := by
  unfold muhammadSat muhammadInvariantLedger
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem muhammad_gap_witness : muhammadGapsExposeBoundary muhammadGapLedger := by
  unfold muhammadGapsExposeBoundary muhammadGapLedger
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem muhammad_access_archaeological :
    muhammadSuraAccess.mode =
      Gnosis.ArchaeologicalInfinityAccess.AccessMode.archaeological := by
  rfl

theorem quran_muhammad_sura_quality_witness :
    muhammadQualityClusters.length = 5 ∧
    muhammadSat muhammadInvariantLedger ∧
    muhammadGapsExposeBoundary muhammadGapLedger ∧
    muhammadSuraAccess.mode =
      Gnosis.ArchaeologicalInfinityAccess.AccessMode.archaeological ∧
    TruthOneManyNamesWitness.manyNamesAgree
      (fun _ : MuhammadRegister => MuhammadInvariant.truthRepairAgainstNullification)
      MuhammadInvariant.truthRepairAgainstNullification := by
  exact ⟨muhammad_quality_clusters_shape.left, muhammad_sat_witness, muhammad_gap_witness,
    muhammad_access_archaeological, muhammadRegistersAgree⟩

end QuranMuhammadSuraQualityWitness
end Gnosis.Witnesses.Islam
