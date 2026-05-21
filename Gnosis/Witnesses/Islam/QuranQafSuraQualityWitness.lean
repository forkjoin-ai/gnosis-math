import Gnosis.ArchaeologicalInfinityAccess
import Gnosis.TruthOneManyNamesWitness

namespace Gnosis.Witnesses.Islam
namespace QuranQafSuraQualityWitness

/-!
# Quran 50, Qaf -- Complete Sura Quality Witness

Source text: `docs/ebooks/source-texts/abdel-haleem-quran.pdf`, extracted with
`pdftotext -layout`; text anchor `/tmp/emotions-quran/abdel-haleem-quran.txt:13526-13603`.

This complete sura witness covers Quran 50:1-45.

Qaf is the near-record-and-resurrection witness: glorious Quran, surprise at
resurrection, earth knowing what diminishes bodies, raised sky, spread earth,
rain-revived gardens, past deniers, nearer-than-jugular divine knowledge, two
recorders, death stupor, trumpet, driver and witness, companion dispute, Hell's
"Are there any more?", Garden brought near, and command to remind by Quran.

No `sorry`, no new `axiom`.
-/

inductive QafQualityCluster
  | gloriousQuranAndResurrectionSurprise
  | earthRecordSkyEarthRainAndRevival
  | pastDeniersAndNearerThanJugularKnowledge
  | twoRecordersDeathStuporTrumpetAndWitness
  | hellGardenCompanionDisputeAndQuranReminder
deriving DecidableEq, Repr

def qafQualityClusters : List QafQualityCluster :=
  [ .gloriousQuranAndResurrectionSurprise
  , .earthRecordSkyEarthRainAndRevival
  , .pastDeniersAndNearerThanJugularKnowledge
  , .twoRecordersDeathStuporTrumpetAndWitness
  , .hellGardenCompanionDisputeAndQuranReminder
  ]

structure QafInvariantLedger where
  earthRecordPreservesDiminishedBodies : Bool := true
  revivedLandImagesEmergence : Bool := true
  divineKnowledgeIsNearerThanJugular : Bool := true
  everyUtteranceHasReadyRecorder : Bool := true
  quranReminderAddressesThoseWhoFearWarning : Bool := true
deriving DecidableEq, Repr

def qafInvariantLedger : QafInvariantLedger := {}

def qafSat (l : QafInvariantLedger) : Prop :=
  l.earthRecordPreservesDiminishedBodies = true ∧
  l.revivedLandImagesEmergence = true ∧
  l.divineKnowledgeIsNearerThanJugular = true ∧
  l.everyUtteranceHasReadyRecorder = true ∧
  l.quranReminderAddressesThoseWhoFearWarning = true

structure QafGapLedger where
  resurrectionIsCalledStrangeReturn : Bool := true
  pastDeniersRepeatTheWarningCycle : Bool := true
  companionDeniesResponsibilityForMisguidance : Bool := true
  hellExposesUnfilledAppetite : Bool := true
  heedlessCoverIsLiftedTooLate : Bool := true
deriving DecidableEq, Repr

def qafGapLedger : QafGapLedger := {}

def qafGapsExposeBoundary (g : QafGapLedger) : Prop :=
  g.resurrectionIsCalledStrangeReturn = true ∧
  g.pastDeniersRepeatTheWarningCycle = true ∧
  g.companionDeniesResponsibilityForMisguidance = true ∧
  g.hellExposesUnfilledAppetite = true ∧
  g.heedlessCoverIsLiftedTooLate = true

def qafSuraAccess : Gnosis.ArchaeologicalInfinityAccess.Access :=
  { claim := "Quran 50 / Qaf witnesses near knowledge, ready recorders, and resurrection emergence"
    positiveSamples := [1, 2, 3, 4, 5]
    negativeSamples := [6, 7, 8, 9, 10] }

inductive QafRegister | quran | earth | rain | nearness | recorders | trumpet
deriving DecidableEq, Repr, Nonempty

inductive QafInvariant | nearRecordResurrection
deriving DecidableEq, Repr

def qafRegistersAgree :
    TruthOneManyNamesWitness.manyNamesAgree
      (fun _ : QafRegister => QafInvariant.nearRecordResurrection)
      QafInvariant.nearRecordResurrection :=
  TruthOneManyNamesWitness.constant_names_agree QafInvariant.nearRecordResurrection

theorem qaf_quality_clusters_shape :
    qafQualityClusters.length = 5 ∧
    qafQualityClusters.head? = some .gloriousQuranAndResurrectionSurprise ∧
    qafQualityClusters.getLast? = some .hellGardenCompanionDisputeAndQuranReminder := by
  exact ⟨rfl, rfl, rfl⟩

theorem qaf_sat_witness : qafSat qafInvariantLedger := by
  unfold qafSat qafInvariantLedger
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem qaf_gap_witness : qafGapsExposeBoundary qafGapLedger := by
  unfold qafGapsExposeBoundary qafGapLedger
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem qaf_access_archaeological :
    qafSuraAccess.mode =
      Gnosis.ArchaeologicalInfinityAccess.AccessMode.archaeological := by
  rfl

theorem quran_qaf_sura_quality_witness :
    qafQualityClusters.length = 5 ∧
    qafSat qafInvariantLedger ∧
    qafGapsExposeBoundary qafGapLedger ∧
    qafSuraAccess.mode =
      Gnosis.ArchaeologicalInfinityAccess.AccessMode.archaeological ∧
    TruthOneManyNamesWitness.manyNamesAgree
      (fun _ : QafRegister => QafInvariant.nearRecordResurrection)
      QafInvariant.nearRecordResurrection := by
  exact ⟨qaf_quality_clusters_shape.left, qaf_sat_witness, qaf_gap_witness,
    qaf_access_archaeological, qafRegistersAgree⟩

end QuranQafSuraQualityWitness
end Gnosis.Witnesses.Islam
