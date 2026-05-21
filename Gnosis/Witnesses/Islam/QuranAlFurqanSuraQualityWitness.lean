import Gnosis.ArchaeologicalInfinityAccess
import Gnosis.TruthOneManyNamesWitness

namespace Gnosis.Witnesses.Islam
namespace QuranAlFurqanSuraQualityWitness

/-!
# Quran 25, Al-Furqan / The Differentiator -- Complete Sura Quality Witness

Source text: `docs/ebooks/source-texts/abdel-haleem-quran.pdf`, extracted with
`pdftotext -layout`; text anchor `/tmp/emotions-quran/abdel-haleem-quran.txt:9527-9701`.

This complete sura witness covers Quran 25:1-77.

Al-Furqan is the differentiation witness. The measured creation and warning
sent to all people separates servant revelation from forged fable, human
messenger from angel demand, gradual revelation from impatience, false friends
from Messenger path, passion-as-god from hearing, and servants of the Lord of
Mercy from those who write off truth. The close lists the true servant topology:
humility, night worship, balanced spending, no partner, no murder, no adultery,
repentance, dignified passage, and prayer for exemplary households.

No `sorry`, no new `axiom`.
-/

inductive AlFurqanQualityCluster
  | differentiatorMeasuredCreationAndFalseGods
  | forgedFableHumanMessengerAndHourDenial
  | falseGodDenialGradualRevelationAndPastWarnings
  | shadeWaterBarrierHumanKinAndTrust
  | lordOfMercyServantsAndRepentanceClose
deriving DecidableEq, Repr

def alFurqanQualityClusters : List AlFurqanQualityCluster :=
  [ AlFurqanQualityCluster.differentiatorMeasuredCreationAndFalseGods
  , AlFurqanQualityCluster.forgedFableHumanMessengerAndHourDenial
  , AlFurqanQualityCluster.falseGodDenialGradualRevelationAndPastWarnings
  , AlFurqanQualityCluster.shadeWaterBarrierHumanKinAndTrust
  , AlFurqanQualityCluster.lordOfMercyServantsAndRepentanceClose
  ]

structure AlFurqanInvariantLedger where
  differentiatorWarnsAllPeople : Bool := true
  creationIsMadeToExactMeasure : Bool := true
  gradualRevelationStrengthensHeart : Bool := true
  quranStruggleCarriesWarning : Bool := true
  lordOfMercyServantsHaveEthicalShape : Bool := true
  repentanceCanTransformEvilIntoGood : Bool := true
deriving DecidableEq, Repr

def alFurqanInvariantLedger : AlFurqanInvariantLedger := {}

def alFurqanSat (l : AlFurqanInvariantLedger) : Prop :=
  l.differentiatorWarnsAllPeople = true ∧
  l.creationIsMadeToExactMeasure = true ∧
  l.gradualRevelationStrengthensHeart = true ∧
  l.quranStruggleCarriesWarning = true ∧
  l.lordOfMercyServantsHaveEthicalShape = true ∧
  l.repentanceCanTransformEvilIntoGood = true

structure AlFurqanGapLedger where
  forgedLieAndAncientFables : Bool := true
  marketWalkingMessengerObjection : Bool := true
  hourRejected : Bool := true
  falseFriendLedFromRevelation : Bool := true
  quranShunnedByPeople : Bool := true
  passionTakenAsGod : Bool := true
  lordOfMercyQuestioned : Bool := true
  truthWrittenOffAsLie : Bool := true
deriving DecidableEq, Repr

def alFurqanGapLedger : AlFurqanGapLedger := {}

def alFurqanGapsExposeBoundary (g : AlFurqanGapLedger) : Prop :=
  g.forgedLieAndAncientFables = true ∧
  g.marketWalkingMessengerObjection = true ∧
  g.hourRejected = true ∧
  g.falseFriendLedFromRevelation = true ∧
  g.quranShunnedByPeople = true ∧
  g.passionTakenAsGod = true ∧
  g.lordOfMercyQuestioned = true ∧
  g.truthWrittenOffAsLie = true

def alFurqanSuraAccess : Gnosis.ArchaeologicalInfinityAccess.Access :=
  { claim := "Quran 25 / Al-Furqan witnesses differentiation between false measures and servants of mercy"
    positiveSamples := [1, 2, 3, 4, 5, 6]
    negativeSamples := [7, 8, 9, 10, 11, 12] }

inductive AlFurqanRegister | measure | messenger | gradual | quran | creation | servants
deriving DecidableEq, Repr, Nonempty

inductive AlFurqanInvariant | differentiatingMercyServanthood
deriving DecidableEq, Repr

def alFurqanRegistersAgree :
    TruthOneManyNamesWitness.manyNamesAgree
      (fun _ : AlFurqanRegister => AlFurqanInvariant.differentiatingMercyServanthood)
      AlFurqanInvariant.differentiatingMercyServanthood :=
  TruthOneManyNamesWitness.constant_names_agree AlFurqanInvariant.differentiatingMercyServanthood

theorem al_furqan_quality_clusters_shape :
    alFurqanQualityClusters.length = 5
    ∧ alFurqanQualityClusters.head? =
      some AlFurqanQualityCluster.differentiatorMeasuredCreationAndFalseGods
    ∧ alFurqanQualityClusters.getLast? =
      some AlFurqanQualityCluster.lordOfMercyServantsAndRepentanceClose := by
  exact ⟨rfl, rfl, rfl⟩

theorem al_furqan_sat_witness : alFurqanSat alFurqanInvariantLedger := by
  unfold alFurqanSat alFurqanInvariantLedger
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem al_furqan_gap_witness : alFurqanGapsExposeBoundary alFurqanGapLedger := by
  unfold alFurqanGapsExposeBoundary alFurqanGapLedger
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem al_furqan_access_archaeological :
    alFurqanSuraAccess.mode =
      Gnosis.ArchaeologicalInfinityAccess.AccessMode.archaeological := by
  rfl

theorem quran_al_furqan_sura_quality_witness :
    alFurqanQualityClusters.length = 5 ∧
    alFurqanSat alFurqanInvariantLedger ∧
    alFurqanGapsExposeBoundary alFurqanGapLedger ∧
    alFurqanSuraAccess.mode =
      Gnosis.ArchaeologicalInfinityAccess.AccessMode.archaeological ∧
    TruthOneManyNamesWitness.manyNamesAgree
      (fun _ : AlFurqanRegister => AlFurqanInvariant.differentiatingMercyServanthood)
      AlFurqanInvariant.differentiatingMercyServanthood := by
  exact ⟨al_furqan_quality_clusters_shape.left, al_furqan_sat_witness,
    al_furqan_gap_witness, al_furqan_access_archaeological, alFurqanRegistersAgree⟩

end QuranAlFurqanSuraQualityWitness
end Gnosis.Witnesses.Islam
