import Gnosis.ArchaeologicalInfinityAccess
import Gnosis.TruthOneManyNamesWitness

namespace Gnosis.Witnesses.Islam
namespace QuranAlKahfSuraQualityWitness

/-!
# Quran 18, Al-Kahf / The Cave -- Complete Sura Quality Witness

Source text: `docs/ebooks/source-texts/abdel-haleem-quran.pdf`, extracted with
`pdftotext -layout`; text anchor `/tmp/emotions-quran/abdel-haleem-quran.txt:7888-8180`.

This complete sura witness covers Quran 18:1-110.

Al-Kahf is the hidden-knowledge and refuge witness. Straight Scripture, the
cave sleepers, "God willing", companionship with the humble, the garden parable,
the opened record, Moses' inability to bear hidden mercy, Dhu'l-Qarnayn's
barrier, and the inexhaustible words of the Lord all expose the limit of surface
judgment. The counterproof is offspring-claim, worldly adornment attachment,
guessing in the dark, arrogant garden security, Iblis as patron, contentious
argument, impatience before explanation, and good-work delusion without meeting.

No `sorry`, no new `axiom`.
-/

inductive AlKahfQualityCluster
  | straightScriptureWarningAndEarthTest
  | sleepersRefugeHeartStrengthAndResurrectionSign
  | godWillingHiddenNumberAndRevealedWords
  | humbleCompanionshipAndFreeChoice
  | gardenParableWorldStubbleAndOpenRecord
  | iblisBadBargainAndContentiousRefusal
  | mosesTwoSeasPatienceAndHiddenMercy
  | dhuAlQarnaynPowerBarrierAndPromise
  | noWeightLosersParadiseAndInexhaustibleWords
deriving DecidableEq, Repr

def alKahfQualityClusters : List AlKahfQualityCluster :=
  [ AlKahfQualityCluster.straightScriptureWarningAndEarthTest
  , AlKahfQualityCluster.sleepersRefugeHeartStrengthAndResurrectionSign
  , AlKahfQualityCluster.godWillingHiddenNumberAndRevealedWords
  , AlKahfQualityCluster.humbleCompanionshipAndFreeChoice
  , AlKahfQualityCluster.gardenParableWorldStubbleAndOpenRecord
  , AlKahfQualityCluster.iblisBadBargainAndContentiousRefusal
  , AlKahfQualityCluster.mosesTwoSeasPatienceAndHiddenMercy
  , AlKahfQualityCluster.dhuAlQarnaynPowerBarrierAndPromise
  , AlKahfQualityCluster.noWeightLosersParadiseAndInexhaustibleWords
  ]

structure AlKahfInvariantLedger where
  scriptureIsUnerringlyStraight : Bool := true
  refugeOpensMercyUnderPressure : Bool := true
  unseenDurationBelongsToGod : Bool := true
  revealedWordsCannotBeChanged : Bool := true
  lastingWorksOutrankWorldAdornments : Bool := true
  hiddenMercyExceedsSurfaceJudgment : Bool := true
  powerIsServiceWhenReturnedToLord : Bool := true
  lordsWordsOutrunOceanInk : Bool := true
deriving DecidableEq, Repr

def alKahfInvariantLedger : AlKahfInvariantLedger := {}

def alKahfSat (l : AlKahfInvariantLedger) : Prop :=
  l.scriptureIsUnerringlyStraight = true ∧
  l.refugeOpensMercyUnderPressure = true ∧
  l.unseenDurationBelongsToGod = true ∧
  l.revealedWordsCannotBeChanged = true ∧
  l.lastingWorksOutrankWorldAdornments = true ∧
  l.hiddenMercyExceedsSurfaceJudgment = true ∧
  l.powerIsServiceWhenReturnedToLord = true ∧
  l.lordsWordsOutrunOceanInk = true

structure AlKahfGapLedger where
  offspringClaimWithoutKnowledge : Bool := true
  worldlyAttractionMisreadAsPermanence : Bool := true
  guessingInTheDark : Bool := true
  eyesTurnFromHumbleBelievers : Bool := true
  arrogantGardenSecurity : Bool := true
  iblisOffspringTakenAsMasters : Bool := true
  falseArgumentsMockWarning : Bool := true
  impatienceBeforeExplanation : Bool := true
  goodWorkDelusionWithoutMeeting : Bool := true
deriving DecidableEq, Repr

def alKahfGapLedger : AlKahfGapLedger := {}

def alKahfGapsExposeBoundary (g : AlKahfGapLedger) : Prop :=
  g.offspringClaimWithoutKnowledge = true ∧
  g.worldlyAttractionMisreadAsPermanence = true ∧
  g.guessingInTheDark = true ∧
  g.eyesTurnFromHumbleBelievers = true ∧
  g.arrogantGardenSecurity = true ∧
  g.iblisOffspringTakenAsMasters = true ∧
  g.falseArgumentsMockWarning = true ∧
  g.impatienceBeforeExplanation = true ∧
  g.goodWorkDelusionWithoutMeeting = true

def alKahfSuraAccess : Gnosis.ArchaeologicalInfinityAccess.Access :=
  { claim := "Quran 18 / Al-Kahf witnesses refuge and hidden mercy beyond surface judgment"
    positiveSamples := [1, 2, 3, 4, 5, 6, 7]
    negativeSamples := [8, 9, 10, 11, 12, 13] }

inductive AlKahfRegister | scripture | cave | hidden | garden | record | moses | barrier | ocean
deriving DecidableEq, Repr, Nonempty

inductive AlKahfInvariant | hiddenMercyRefuge
deriving DecidableEq, Repr

def alKahfRegistersAgree :
    TruthOneManyNamesWitness.manyNamesAgree
      (fun _ : AlKahfRegister => AlKahfInvariant.hiddenMercyRefuge)
      AlKahfInvariant.hiddenMercyRefuge :=
  TruthOneManyNamesWitness.constant_names_agree AlKahfInvariant.hiddenMercyRefuge

theorem al_kahf_quality_clusters_shape :
    alKahfQualityClusters.length = 9
    ∧ alKahfQualityClusters.head? =
      some AlKahfQualityCluster.straightScriptureWarningAndEarthTest
    ∧ alKahfQualityClusters.getLast? =
      some AlKahfQualityCluster.noWeightLosersParadiseAndInexhaustibleWords := by
  exact ⟨rfl, rfl, rfl⟩

theorem al_kahf_sat_witness : alKahfSat alKahfInvariantLedger := by
  unfold alKahfSat alKahfInvariantLedger
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem al_kahf_gap_witness : alKahfGapsExposeBoundary alKahfGapLedger := by
  unfold alKahfGapsExposeBoundary alKahfGapLedger
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem al_kahf_access_archaeological :
    alKahfSuraAccess.mode =
      Gnosis.ArchaeologicalInfinityAccess.AccessMode.archaeological := by
  rfl

theorem quran_al_kahf_sura_quality_witness :
    alKahfQualityClusters.length = 9 ∧
    alKahfSat alKahfInvariantLedger ∧
    alKahfGapsExposeBoundary alKahfGapLedger ∧
    alKahfSuraAccess.mode =
      Gnosis.ArchaeologicalInfinityAccess.AccessMode.archaeological ∧
    TruthOneManyNamesWitness.manyNamesAgree
      (fun _ : AlKahfRegister => AlKahfInvariant.hiddenMercyRefuge)
      AlKahfInvariant.hiddenMercyRefuge := by
  exact ⟨al_kahf_quality_clusters_shape.left, al_kahf_sat_witness, al_kahf_gap_witness,
    al_kahf_access_archaeological, alKahfRegistersAgree⟩

end QuranAlKahfSuraQualityWitness
end Gnosis.Witnesses.Islam
