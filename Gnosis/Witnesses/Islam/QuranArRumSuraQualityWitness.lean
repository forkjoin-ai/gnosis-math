import Gnosis.ArchaeologicalInfinityAccess
import Gnosis.TruthOneManyNamesWitness

namespace Gnosis.Witnesses.Islam
namespace QuranArRumSuraQualityWitness

/-!
# Quran 30, Ar-Rum / The Byzantines -- Complete Sura Quality Witness

Source text: `docs/ebooks/source-texts/abdel-haleem-quran.pdf`, extracted with
`pdftotext -layout`; text anchor `/tmp/emotions-quran/abdel-haleem-quran.txt:10610-10763`.

This complete sura witness covers Quran 30:1-60.

Ar-Rum is the promise-and-signs witness. Byzantine reversal, serious creation,
living/dead alternation, spouses, language/color diversity, sleep, lightning,
earth revival, fitra, charity over usury, corruption on land and sea, mercy
imprints in rain, human life stages, and patient trust in God's promise all
expose the difference between surface knowledge and the true life.

No `sorry`, no new `axiom`.
-/

inductive ArRumQualityCluster
  | byzantinePromiseSurfaceKnowledgeAndReturn
  | glorificationLivingDeadAndCreationSigns
  | fitraSectsHardshipShirkAndCharity
  | corruptionMercyRainAndDeafBlindLimit
  | hourExcusesIllustrationsAndPatientPromise
deriving DecidableEq, Repr

def arRumQualityClusters : List ArRumQualityCluster :=
  [ ArRumQualityCluster.byzantinePromiseSurfaceKnowledgeAndReturn
  , ArRumQualityCluster.glorificationLivingDeadAndCreationSigns
  , ArRumQualityCluster.fitraSectsHardshipShirkAndCharity
  , ArRumQualityCluster.corruptionMercyRainAndDeafBlindLimit
  , ArRumQualityCluster.hourExcusesIllustrationsAndPatientPromise
  ]

structure ArRumInvariantLedger where
  godPromiseDoesNotBreak : Bool := true
  creationHasSeriousPurposeAndAppointedTime : Bool := true
  signsAppearInSelvesSpousesLanguagesSleepAndRain : Bool := true
  fitraCannotBeAltered : Bool := true
  charitySeekingGodsFaceMultiplies : Bool := true
  mercyRevivesEarthAsResurrectionSign : Bool := true
  patienceRestsOnTruePromise : Bool := true
deriving DecidableEq, Repr

def arRumInvariantLedger : ArRumInvariantLedger := {}

def arRumSat (l : ArRumInvariantLedger) : Prop :=
  l.godPromiseDoesNotBreak = true ∧
  l.creationHasSeriousPurposeAndAppointedTime = true ∧
  l.signsAppearInSelvesSpousesLanguagesSleepAndRain = true ∧
  l.fitraCannotBeAltered = true ∧
  l.charitySeekingGodsFaceMultiplies = true ∧
  l.mercyRevivesEarthAsResurrectionSign = true ∧
  l.patienceRestsOnTruePromise = true

structure ArRumGapLedger where
  outerSurfaceKnowledgeOnly : Bool := true
  meetingLordDenied : Bool := true
  partnersDeniedByPartners : Bool := true
  desiresFollowedWithoutKnowledge : Bool := true
  religionSplitIntoSects : Bool := true
  hardshipReliefTurnsToShirk : Bool := true
  usuryGainFailsWithGod : Bool := true
  noFirmBeliefDiscouragement : Bool := true
deriving DecidableEq, Repr

def arRumGapLedger : ArRumGapLedger := {}

def arRumGapsExposeBoundary (g : ArRumGapLedger) : Prop :=
  g.outerSurfaceKnowledgeOnly = true ∧
  g.meetingLordDenied = true ∧
  g.partnersDeniedByPartners = true ∧
  g.desiresFollowedWithoutKnowledge = true ∧
  g.religionSplitIntoSects = true ∧
  g.hardshipReliefTurnsToShirk = true ∧
  g.usuryGainFailsWithGod = true ∧
  g.noFirmBeliefDiscouragement = true

def arRumSuraAccess : Gnosis.ArchaeologicalInfinityAccess.Access :=
  { claim := "Quran 30 / Ar-Rum witnesses true promise, creation signs, fitra, and patient certainty"
    positiveSamples := [1, 2, 3, 4, 5, 6]
    negativeSamples := [7, 8, 9, 10, 11, 12] }

inductive ArRumRegister | promise | signs | fitra | charity | corruption | mercy | patience
deriving DecidableEq, Repr, Nonempty

inductive ArRumInvariant | promiseSignsFitraPatience
deriving DecidableEq, Repr

def arRumRegistersAgree :
    TruthOneManyNamesWitness.manyNamesAgree
      (fun _ : ArRumRegister => ArRumInvariant.promiseSignsFitraPatience)
      ArRumInvariant.promiseSignsFitraPatience :=
  TruthOneManyNamesWitness.constant_names_agree ArRumInvariant.promiseSignsFitraPatience

theorem ar_rum_quality_clusters_shape :
    arRumQualityClusters.length = 5
    ∧ arRumQualityClusters.head? =
      some ArRumQualityCluster.byzantinePromiseSurfaceKnowledgeAndReturn
    ∧ arRumQualityClusters.getLast? =
      some ArRumQualityCluster.hourExcusesIllustrationsAndPatientPromise := by
  exact ⟨rfl, rfl, rfl⟩

theorem ar_rum_sat_witness : arRumSat arRumInvariantLedger := by
  unfold arRumSat arRumInvariantLedger
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem ar_rum_gap_witness : arRumGapsExposeBoundary arRumGapLedger := by
  unfold arRumGapsExposeBoundary arRumGapLedger
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem ar_rum_access_archaeological :
    arRumSuraAccess.mode =
      Gnosis.ArchaeologicalInfinityAccess.AccessMode.archaeological := by
  rfl

theorem quran_ar_rum_sura_quality_witness :
    arRumQualityClusters.length = 5 ∧
    arRumSat arRumInvariantLedger ∧
    arRumGapsExposeBoundary arRumGapLedger ∧
    arRumSuraAccess.mode =
      Gnosis.ArchaeologicalInfinityAccess.AccessMode.archaeological ∧
    TruthOneManyNamesWitness.manyNamesAgree
      (fun _ : ArRumRegister => ArRumInvariant.promiseSignsFitraPatience)
      ArRumInvariant.promiseSignsFitraPatience := by
  exact ⟨ar_rum_quality_clusters_shape.left, ar_rum_sat_witness, ar_rum_gap_witness,
    ar_rum_access_archaeological, arRumRegistersAgree⟩

end QuranArRumSuraQualityWitness
end Gnosis.Witnesses.Islam
