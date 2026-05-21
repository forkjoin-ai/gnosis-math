import Gnosis.Witnesses.Chaldean.DelugeSeventhDayBirdProbeWitness
import Gnosis.Witnesses.Chaldean.HeaAlternativeJudgmentWitness

namespace Gnosis.Witnesses.Chaldean
namespace ComparativeFloodMethodReserveWitness

/-!
# Comparative Flood Method Reserve Witness

Source surface:
`docs/ebooks/source-texts/chaldean-account-of-genesis-smith.txt`, Chapter XII
conclusion, Smith's comparison of Genesis, Berosus, and the cuneiform Flood
tablet.

Smith's method is unusually useful for witness work. He grants correspondence,
but refuses superficial comparison, confesses limits in Biblical criticism,
notes prejudice in the scholarly field, and marks a vanished mediator network:
between Chaldea and Palestine lay Aramean and Hittite peoples whose histories,
mythologies, and traditions are largely lost. That missing middle matters. It
prevents a cheap direct-copy story while strengthening the case for a distributed
tradition graph.

The source also states that differences cannot be explained away: ark size,
saved passengers, duration, mountain location, bird sequence, religious system,
and patriarch translation diverge. Correspondence plus difference is the method:
shared event topology, local carrier coloring, lost mediator traditions.

No `sorry`, no new `axiom`.
-/

structure ComparativeReserve where
  priorComparisonsCalledSuperficial : Bool := true
  criticalExaminationOfBothTextsRequired : Bool := true
  biblicalCriticismCompetenceReserved : Bool := true
  scholarlyPrejudiceNamed : Bool := true
  noPrevailingViewAdoptedAsFact : Bool := true
deriving DecidableEq, Repr

def comparativeReserve : ComparativeReserve := {}

def comparisonHeldUnderReserve (c : ComparativeReserve) : Prop :=
  c.priorComparisonsCalledSuperficial = true ∧
  c.criticalExaminationOfBothTextsRequired = true ∧
  c.biblicalCriticismCompetenceReserved = true ∧
  c.scholarlyPrejudiceNamed = true ∧
  c.noPrevailingViewAdoptedAsFact = true

structure LostMediatorTraditions where
  chaldeaPalestineDistanceNamed : Bool := true
  connectingNationsNamed : Bool := true
  arameanRaceNamed : Bool := true
  hittiteRaceNamed : Bool := true
  historiesLost : Bool := true
  mythologiesAndTraditionsUnknown : Bool := true
  futureResearchRequired : Bool := true
deriving DecidableEq, Repr

def lostMediatorTraditions : LostMediatorTraditions := {}

def mediatorArchiveHole (m : LostMediatorTraditions) : Prop :=
  m.chaldeaPalestineDistanceNamed = true ∧
  m.connectingNationsNamed = true ∧
  m.arameanRaceNamed = true ∧
  m.hittiteRaceNamed = true ∧
  m.historiesLost = true ∧
  m.mythologiesAndTraditionsUnknown = true ∧
  m.futureResearchRequired = true

structure CorrespondenceWithoutDirectCopy where
  connectionOfSomeSortAdmitted : Bool := true
  independentTestimonyEarlierThanOtherEvidence : Bool := true
  differencesExpectedFromPlaceAndReligion : Bool := true
  cuneiformDiffersFromBerosusToo : Bool := true
  neitherDocumentDirectCopy : Bool := true
deriving DecidableEq, Repr

def correspondenceWithoutDirectCopy : CorrespondenceWithoutDirectCopy := {}

def sharedTopologyWithoutCopyClaim (s : CorrespondenceWithoutDirectCopy) : Prop :=
  s.connectionOfSomeSortAdmitted = true ∧
  s.independentTestimonyEarlierThanOtherEvidence = true ∧
  s.differencesExpectedFromPlaceAndReligion = true ∧
  s.cuneiformDiffersFromBerosusToo = true ∧
  s.neitherDocumentDirectCopy = true

structure DivergenceLedger where
  arkSizeDiffers : Bool := true
  savedPassengersDiffer : Bool := true
  durationDiffers : Bool := true
  mountainLocationDiffers : Bool := true
  birdSequenceDiffers : Bool := true
  religiousSystemDiffers : Bool := true
  patriarchTranslationDiffers : Bool := true
deriving DecidableEq, Repr

def divergenceLedger : DivergenceLedger := {}

def differencesCannotBeExplainedAway (d : DivergenceLedger) : Prop :=
  d.arkSizeDiffers = true ∧
  d.savedPassengersDiffer = true ∧
  d.durationDiffers = true ∧
  d.mountainLocationDiffers = true ∧
  d.birdSequenceDiffers = true ∧
  d.religiousSystemDiffers = true ∧
  d.patriarchTranslationDiffers = true

theorem comparative_comparison_held_under_reserve :
    comparisonHeldUnderReserve comparativeReserve := by
  unfold comparisonHeldUnderReserve comparativeReserve
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem comparative_mediator_archive_hole :
    mediatorArchiveHole lostMediatorTraditions := by
  unfold mediatorArchiveHole lostMediatorTraditions
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem comparative_shared_topology_without_copy_claim :
    sharedTopologyWithoutCopyClaim correspondenceWithoutDirectCopy := by
  unfold sharedTopologyWithoutCopyClaim correspondenceWithoutDirectCopy
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem comparative_differences_cannot_be_explained_away :
    differencesCannotBeExplainedAway divergenceLedger := by
  unfold differencesCannotBeExplainedAway divergenceLedger
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem comparative_inherits_deluge_topology :
    DelugeSeventhDayBirdProbeWitness.shipPreservesState
      DelugeSeventhDayBirdProbeWitness.sealedShipCarrier ∧
    HeaAlternativeJudgmentWitness.localResponsibilityPreserved
      HeaAlternativeJudgmentWitness.responsibilityGradient ∧
    sharedTopologyWithoutCopyClaim correspondenceWithoutDirectCopy := by
  exact ⟨DelugeSeventhDayBirdProbeWitness.deluge_ship_preserves_state,
    HeaAlternativeJudgmentWitness.hea_local_responsibility_preserved,
    comparative_shared_topology_without_copy_claim⟩

theorem comparative_flood_method_reserve_witness :
    comparisonHeldUnderReserve comparativeReserve ∧
    mediatorArchiveHole lostMediatorTraditions ∧
    sharedTopologyWithoutCopyClaim correspondenceWithoutDirectCopy ∧
    differencesCannotBeExplainedAway divergenceLedger := by
  exact ⟨comparative_comparison_held_under_reserve,
    comparative_mediator_archive_hole,
    comparative_shared_topology_without_copy_claim,
    comparative_differences_cannot_be_explained_away⟩

end ComparativeFloodMethodReserveWitness
end Gnosis.Witnesses.Chaldean
