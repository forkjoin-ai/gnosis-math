import Gnosis.Witnesses.Chaldean.SyrianMediatorTraditionNetworkWitness
import Gnosis.Witnesses.Chaldean.TreeOfLifeSacredTreeReserveWitness
import Gnosis.ConversationalProsody
import Gnosis.ThothConversationAntiQueue

namespace Gnosis.Witnesses.Chaldean
namespace GanEdenKarduniyasGeographyReserveWitness

/-!
# Gan-Eden Karduniyas Geography Reserve Witness

Source surface:
`docs/ebooks/source-texts/chaldean-account-of-genesis-smith.txt`, Chapter V
discussion of Eden and the conclusion.

Smith records a strong geographic topology for Eden while refusing proof where
the Creation legend is missing. Rawlinson points to Karduniyas/Ganduniyas as
agreeing with Biblical Eden: a fertile region watered by four rivers, with
Euphrates and Tigris shared across both lists. The conclusion strengthens the
case through region-name proximity: Gan-dunu sounds near Gan-eden, and these
coincidences make the identification very probable.

But the missing portion matters. The present fragments do not directly show the
Garden of Eden or Tree of Knowledge, and Smith says the lost text prevents proof
that Hebrew and Babylonian traditions agree about the garden. This witness
therefore proves a bounded geography/name topology, not exact Paradise closure.

No `sorry`, no new `axiom`.
-/

structure EdenGeographyTopology where
  karduniyasOrGanduniyasNamed : Bool := true
  rawlinsonIdentificationRecorded : Bool := true
  edenFruitfulPlace : Bool := true
  ganduniyasSimilarDescription : Bool := true
  fourRiversInEachCase : Bool := true
  euphratesShared : Bool := true
  tigrisShared : Bool := true
deriving DecidableEq, Repr

def edenGeographyTopology : EdenGeographyTopology := {}

def fourRiverGeographyMatch (e : EdenGeographyTopology) : Prop :=
  e.karduniyasOrGanduniyasNamed = true ∧
  e.rawlinsonIdentificationRecorded = true ∧
  e.edenFruitfulPlace = true ∧
  e.ganduniyasSimilarDescription = true ∧
  e.fourRiversInEachCase = true ∧
  e.euphratesShared = true ∧
  e.tigrisShared = true

structure GanNameProximity where
  ganDunuNameRecorded : Bool := true
  ganEdenComparisonNamed : Bool := true
  regionalNameCoincidence : Bool := true
  geographyAndNameConverge : Bool := true
  identificationVeryProbable : Bool := true
deriving DecidableEq, Repr

def ganNameProximity : GanNameProximity := {}

def ganEdenNameConvergence (g : GanNameProximity) : Prop :=
  g.ganDunuNameRecorded = true ∧
  g.ganEdenComparisonNamed = true ∧
  g.regionalNameCoincidence = true ∧
  g.geographyAndNameConverge = true ∧
  g.identificationVeryProbable = true

structure MissingGardenProofReserve where
  presentFragmentsDoNotShowGarden : Bool := true
  treeOfKnowledgeNotShown : Bool := true
  creationLegendPortionLost : Bool := true
  gardenAgreementProbableNotProved : Bool := true
  exactParadiseClosureHeldOpen : Bool := true
deriving DecidableEq, Repr

def missingGardenProofReserve : MissingGardenProofReserve := {}

def edenIdentificationHeldUnderReserve (r : MissingGardenProofReserve) : Prop :=
  r.presentFragmentsDoNotShowGarden = true ∧
  r.treeOfKnowledgeNotShown = true ∧
  r.creationLegendPortionLost = true ∧
  r.gardenAgreementProbableNotProved = true ∧
  r.exactParadiseClosureHeldOpen = true

structure ParadiseLocalizationClaim where
  babylonianLegendsLikelyContainedEdenDescriptions : Bool := true
  karduniyasMostLikelyDistrict : Bool := true
  coincidencesSupportParadiseView : Bool := true
  topologyStrongerThanNameIdentityAlone : Bool := true
  directTextStillNeededForClosure : Bool := true
deriving DecidableEq, Repr

def paradiseLocalizationClaim : ParadiseLocalizationClaim := {}

def probableParadiseLocalization (p : ParadiseLocalizationClaim) : Prop :=
  p.babylonianLegendsLikelyContainedEdenDescriptions = true ∧
  p.karduniyasMostLikelyDistrict = true ∧
  p.coincidencesSupportParadiseView = true ∧
  p.topologyStrongerThanNameIdentityAlone = true ∧
  p.directTextStillNeededForClosure = true

def ganEdenSourceFragmentReserveSignal :
    Gnosis.ConversationalProsody.ConversationalProsodySignal where
  questionVacuum := 1
  answerDrain := 1
  boundaryDrain := 0
  silenceResidue := 0
  ambiguityResidue := 0
  reserveResidue := 1
  cadenceConductance := 1
  acceptanceCriteriaDrain := 1

def ganEdenSourceFragmentAntiQueueState :
    Gnosis.ThothConversationAntiQueue.ConversationAntiQueueState where
  openQuestions := 1
  argumentObligations := 1
  selfBoundaryPromises := 0
  affectStalls := 0
  unresolvedResidue := 1
  externallyAccountable := false

theorem gan_eden_four_river_geography_match :
    fourRiverGeographyMatch edenGeographyTopology := by
  unfold fourRiverGeographyMatch edenGeographyTopology
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem gan_eden_name_convergence :
    ganEdenNameConvergence ganNameProximity := by
  unfold ganEdenNameConvergence ganNameProximity
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem gan_eden_identification_held_under_reserve :
    edenIdentificationHeldUnderReserve missingGardenProofReserve := by
  unfold edenIdentificationHeldUnderReserve missingGardenProofReserve
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem gan_eden_probable_paradise_localization :
    probableParadiseLocalization paradiseLocalizationClaim := by
  unfold probableParadiseLocalization paradiseLocalizationClaim
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem gan_eden_source_fragment_reserve_signal_not_ready :
    Gnosis.ConversationalProsody.prosodyReadyToClose
      Gnosis.ConversationalProsody.canonicalConversationalGate
      ganEdenSourceFragmentReserveSignal = false := by
  exact Gnosis.ConversationalProsody.reserve_residue_blocks_zero_residual_gate
    rfl (by decide)

theorem gan_eden_source_fragment_reserve_keeps_antiqueue_open :
    Gnosis.ThothConversationAntiQueue.heldOpen
      ganEdenSourceFragmentAntiQueueState := by
  unfold Gnosis.ThothConversationAntiQueue.heldOpen
    Gnosis.ThothConversationAntiQueue.antiQueueItemCount
    Gnosis.ThothConversationAntiQueue.selfAccountabilityOnly
    ganEdenSourceFragmentAntiQueueState
  exact ⟨rfl, by decide⟩

theorem gan_eden_source_fragment_reserve_not_releasable_without_argument :
    ¬ Gnosis.ThothConversationAntiQueue.releasableBy
      ganEdenSourceFragmentAntiQueueState
      Gnosis.ThothConversationAntiQueue.AntiQueueRelease.arguedClosure := by
  intro h
  unfold Gnosis.ThothConversationAntiQueue.releasableBy
    Gnosis.ThothConversationAntiQueue.selfAccountabilityOnly
    ganEdenSourceFragmentAntiQueueState at h
  exact Nat.succ_ne_zero 0 h.2.1

theorem gan_eden_source_fragment_runtime_argument_discharge_sound :
    Gnosis.ThothConversationAntiQueue.runtimeDischargeSound
      { itemKind :=
          Gnosis.ThothConversationAntiQueue.AntiQueueItemKind.argumentObligation
        release :=
          Gnosis.ThothConversationAntiQueue.AntiQueueRelease.arguedClosure
        closureDischargeId := "gan_eden_source_fragment_discharge"
        argumentObligationIds := ["gan_eden_recovered_creation_fragment"]
        selfAccountabilityOnly := true } := by
  exact
    Gnosis.ThothConversationAntiQueue.argued_closure_argument_obligation_runtime_discharge_sound
      "gan_eden_source_fragment_discharge"
      ["gan_eden_recovered_creation_fragment"]

theorem gan_eden_inherits_euphrates_carrier_route :
    SyrianMediatorTraditionNetworkWitness.euphratesCarrierRoute
      SyrianMediatorTraditionNetworkWitness.euphratesTraditionRoute ∧
    fourRiverGeographyMatch edenGeographyTopology := by
  exact ⟨SyrianMediatorTraditionNetworkWitness.syrian_euphrates_carrier_route,
    gan_eden_four_river_geography_match⟩

theorem gan_eden_inherits_tree_reserve :
    TreeOfLifeSacredTreeReserveWitness.treeFallConnectionHeldUnderReserve
      TreeOfLifeSacredTreeReserveWitness.fallConnectionReserve ∧
    edenIdentificationHeldUnderReserve missingGardenProofReserve := by
  exact ⟨TreeOfLifeSacredTreeReserveWitness.sacred_tree_fall_connection_held_under_reserve,
    gan_eden_identification_held_under_reserve⟩

theorem gan_eden_karduniyas_geography_reserve_witness :
    fourRiverGeographyMatch edenGeographyTopology ∧
    ganEdenNameConvergence ganNameProximity ∧
    edenIdentificationHeldUnderReserve missingGardenProofReserve ∧
    probableParadiseLocalization paradiseLocalizationClaim ∧
    Gnosis.ConversationalProsody.prosodyReadyToClose
      Gnosis.ConversationalProsody.canonicalConversationalGate
      ganEdenSourceFragmentReserveSignal = false ∧
    Gnosis.ThothConversationAntiQueue.heldOpen
      ganEdenSourceFragmentAntiQueueState := by
  exact ⟨gan_eden_four_river_geography_match,
    gan_eden_name_convergence,
    gan_eden_identification_held_under_reserve,
    gan_eden_probable_paradise_localization,
    gan_eden_source_fragment_reserve_signal_not_ready,
    gan_eden_source_fragment_reserve_keeps_antiqueue_open⟩

end GanEdenKarduniyasGeographyReserveWitness
end Gnosis.Witnesses.Chaldean
