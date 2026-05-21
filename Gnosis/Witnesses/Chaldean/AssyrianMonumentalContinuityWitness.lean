import Gnosis.Witnesses.Chaldean.GanEdenKarduniyasGeographyReserveWitness
import Gnosis.Witnesses.Chaldean.KarkartiamatDragonSeaMonsterWitness
import Gnosis.Witnesses.Chaldean.OannesSeaTeacherUnrecoveredWitness
import Gnosis.Witnesses.Chaldean.TreeOfLifeSacredTreeReserveWitness
import Gnosis.ConversationalProsody
import Gnosis.ThothConversationAntiQueue

namespace Gnosis.Witnesses.Chaldean
namespace AssyrianMonumentalContinuityWitness

/-!
# Assyrian Monumental Continuity Witness

Source surface:
`docs/ebooks/source-texts/chaldean-account-of-genesis-smith.txt`, conclusion,
especially the transition from legendary/traditional age to monumental evidence.

Smith marks a carrier transition. The legendary and traditional age ends around
the rise of Urukh of Ur and the monumental era; around that time the stories
appear to have been committed to writing. The witness then survives through
hundreds of seals, early Babylonian cylinders, later Assyrian seals, Egyptian
name traces, and the Assyrian revival's wall, temple, portal, and vase imagery.

The image ledger is not decorative filler. Smith says the seal scenes show that
the legends were well known and part of the country's literature. The Assyrians
carved the sacred tree and cherubim, temple scenes of Merodach and the dragon,
Oannes and the eagle-headed man, Nimrod strangling a lion, and Nimrod/Heabani
struggles with lion and bull. Broken tablets are not the only carrier.

Smith makes the archaeological method explicit by comparing this to Greek
temple sculpture, vase painting, and gem carving: myths furnish subject matter
for artists. That gives continued evidence down to Assurbanipal's Nineveh
library copies, while earlier Babylonian search remains an open reserve.

No `sorry`, no new `axiom`.
-/

structure MonumentalEraTransition where
  urukhBeginsMonumentalEra : Bool := true
  legendaryTraditionalAgeEnds : Bool := true
  storiesCommittedToWriting : Bool := true
  evidenceTrackedToSeventhCentury : Bool := true
  carrierShiftFromOralToMaterial : Bool := true
deriving DecidableEq, Repr

def monumentalEraTransition : MonumentalEraTransition := {}

def oralToMonumentalCarrierShift (m : MonumentalEraTransition) : Prop :=
  m.urukhBeginsMonumentalEra = true ∧
  m.legendaryTraditionalAgeEnds = true ∧
  m.storiesCommittedToWriting = true ∧
  m.evidenceTrackedToSeventhCentury = true ∧
  m.carrierShiftFromOralToMaterial = true

structure SealContinuityLedger where
  hundredsOfSealsInMuseums : Bool := true
  earlyScenesFromGenesisLegends : Bool := true
  someOlderThanBc2000 : Bool := true
  datesContinueToBc1500 : Bool := true
  babylonianAndAssyrianSealsBothUsed : Bool := true
  legendsWellKnownInLiterature : Bool := true
deriving DecidableEq, Repr

def sealContinuityLedger : SealContinuityLedger := {}

def sealsPreserveLegendContinuity (s : SealContinuityLedger) : Prop :=
  s.hundredsOfSealsInMuseums = true ∧
  s.earlyScenesFromGenesisLegends = true ∧
  s.someOlderThanBc2000 = true ∧
  s.datesContinueToBc1500 = true ∧
  s.babylonianAndAssyrianSealsBothUsed = true ∧
  s.legendsWellKnownInLiterature = true

structure InterveningTransmissionBridge where
  babylonianEvidenceGapAfterBc1500 : Bool := true
  egyptianNoticesPreserveKnowledge : Bool := true
  kazartuHunterMayReflectNimrodFame : Bool := true
  egyptianNimrodNamesAppear : Bool := true
  continuityHeldWithReserve : Bool := true
deriving DecidableEq, Repr

def interveningTransmissionBridge : InterveningTransmissionBridge := {}

def knowledgeSurvivesEvidenceGap (b : InterveningTransmissionBridge) : Prop :=
  b.babylonianEvidenceGapAfterBc1500 = true ∧
  b.egyptianNoticesPreserveKnowledge = true ∧
  b.kazartuHunterMayReflectNimrodFame = true ∧
  b.egyptianNimrodNamesAppear = true ∧
  b.continuityHeldWithReserve = true

structure AssyrianRevivalImageProgram where
  referencesResumeAroundBc990 : Bool := true
  referencesContinueThroughEmpire : Bool := true
  sacredTreeAndCherubimOnWalls : Bool := true
  merodachDragonTempleScene : Bool := true
  oannesAndEagleHeadedManDepicted : Bool := true
  nimrodLionPortalFigure : Bool := true
  nimrodHeabaniLionBullVases : Bool := true
deriving DecidableEq, Repr

def assyrianRevivalImageProgram : AssyrianRevivalImageProgram := {}

def monumentalImagesCarryLegends (a : AssyrianRevivalImageProgram) : Prop :=
  a.referencesResumeAroundBc990 = true ∧
  a.referencesContinueThroughEmpire = true ∧
  a.sacredTreeAndCherubimOnWalls = true ∧
  a.merodachDragonTempleScene = true ∧
  a.oannesAndEagleHeadedManDepicted = true ∧
  a.nimrodLionPortalFigure = true ∧
  a.nimrodHeabaniLionBullVases = true

structure ArtContinuityMethod where
  greekArtAnalogyNamed : Bool := true
  mythsFurnishSculptorMaterial : Bool := true
  mythsFurnishEngraverMaterial : Bool := true
  mythsFurnishPainterMaterial : Bool := true
  continuedEvidenceToAssurbanipal : Bool := true
  ninevehLibraryCopiesMade : Bool := true
  earlierBabylonianCopiesExpectedButUnsearched : Bool := true
deriving DecidableEq, Repr

def artContinuityMethod : ArtContinuityMethod := {}

def artLedgerExtendsTextWitness (a : ArtContinuityMethod) : Prop :=
  a.greekArtAnalogyNamed = true ∧
  a.mythsFurnishSculptorMaterial = true ∧
  a.mythsFurnishEngraverMaterial = true ∧
  a.mythsFurnishPainterMaterial = true ∧
  a.continuedEvidenceToAssurbanipal = true ∧
  a.ninevehLibraryCopiesMade = true ∧
  a.earlierBabylonianCopiesExpectedButUnsearched = true

def assyrianContinuityReserveSignal :
    Gnosis.ConversationalProsody.ConversationalProsodySignal where
  questionVacuum := 1
  answerDrain := 1
  boundaryDrain := 0
  silenceResidue := 0
  ambiguityResidue := 0
  reserveResidue := 1
  cadenceConductance := 1
  acceptanceCriteriaDrain := 1

def assyrianContinuityAntiQueueState :
    Gnosis.ThothConversationAntiQueue.ConversationAntiQueueState where
  openQuestions := 1
  argumentObligations := 1
  selfBoundaryPromises := 0
  affectStalls := 0
  unresolvedResidue := 1
  externallyAccountable := false

theorem assyrian_oral_to_monumental_carrier_shift :
    oralToMonumentalCarrierShift monumentalEraTransition := by
  unfold oralToMonumentalCarrierShift monumentalEraTransition
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem assyrian_seals_preserve_legend_continuity :
    sealsPreserveLegendContinuity sealContinuityLedger := by
  unfold sealsPreserveLegendContinuity sealContinuityLedger
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem assyrian_knowledge_survives_evidence_gap :
    knowledgeSurvivesEvidenceGap interveningTransmissionBridge := by
  unfold knowledgeSurvivesEvidenceGap interveningTransmissionBridge
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem assyrian_monumental_images_carry_legends :
    monumentalImagesCarryLegends assyrianRevivalImageProgram := by
  unfold monumentalImagesCarryLegends assyrianRevivalImageProgram
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem assyrian_art_ledger_extends_text_witness :
    artLedgerExtendsTextWitness artContinuityMethod := by
  unfold artLedgerExtendsTextWitness artContinuityMethod
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem assyrian_continuity_reserve_signal_not_ready :
    Gnosis.ConversationalProsody.prosodyReadyToClose
      Gnosis.ConversationalProsody.canonicalConversationalGate
      assyrianContinuityReserveSignal = false := by
  exact Gnosis.ConversationalProsody.reserve_residue_blocks_zero_residual_gate
    rfl (by decide)

theorem assyrian_continuity_reserve_keeps_antiqueue_open :
    Gnosis.ThothConversationAntiQueue.heldOpen
      assyrianContinuityAntiQueueState := by
  unfold Gnosis.ThothConversationAntiQueue.heldOpen
    Gnosis.ThothConversationAntiQueue.antiQueueItemCount
    Gnosis.ThothConversationAntiQueue.selfAccountabilityOnly
    assyrianContinuityAntiQueueState
  exact ⟨rfl, by decide⟩

theorem assyrian_continuity_reserve_not_releasable_without_argument :
    ¬ Gnosis.ThothConversationAntiQueue.releasableBy
      assyrianContinuityAntiQueueState
      Gnosis.ThothConversationAntiQueue.AntiQueueRelease.arguedClosure := by
  intro h
  unfold Gnosis.ThothConversationAntiQueue.releasableBy
    Gnosis.ThothConversationAntiQueue.selfAccountabilityOnly
    assyrianContinuityAntiQueueState at h
  exact Nat.succ_ne_zero 0 h.2.1

theorem assyrian_continuity_runtime_argument_discharge_sound :
    Gnosis.ThothConversationAntiQueue.runtimeDischargeSound
      { itemKind :=
          Gnosis.ThothConversationAntiQueue.AntiQueueItemKind.argumentObligation
        release :=
          Gnosis.ThothConversationAntiQueue.AntiQueueRelease.arguedClosure
        closureDischargeId := "assyrian_continuity_search_discharge"
        argumentObligationIds := ["assyrian_earlier_babylonian_copy_evidence"]
        selfAccountabilityOnly := true } := by
  exact
    Gnosis.ThothConversationAntiQueue.argued_closure_argument_obligation_runtime_discharge_sound
      "assyrian_continuity_search_discharge"
      ["assyrian_earlier_babylonian_copy_evidence"]

theorem assyrian_inherits_sacred_tree_image_ledger :
    TreeOfLifeSacredTreeReserveWitness.sacredTreeRecursAcrossMedia
      TreeOfLifeSacredTreeReserveWitness.sacredTreeEmblemRecurrence ∧
    monumentalImagesCarryLegends assyrianRevivalImageProgram := by
  exact ⟨TreeOfLifeSacredTreeReserveWitness.sacred_tree_recurs_across_media,
    assyrian_monumental_images_carry_legends⟩

theorem assyrian_inherits_dragon_and_oannes_carriers :
    KarkartiamatDragonSeaMonsterWitness.seaDragonCarriesFallVector
      KarkartiamatDragonSeaMonsterWitness.dragonFallVector ∧
    OannesSeaTeacherUnrecoveredWitness.oannesSeaTeacher
      OannesSeaTeacherUnrecoveredWitness.seaTeacherComposite ∧
    monumentalImagesCarryLegends assyrianRevivalImageProgram := by
  exact ⟨KarkartiamatDragonSeaMonsterWitness.karkartiamat_carries_fall_vector,
    OannesSeaTeacherUnrecoveredWitness.oannes_sea_teacher,
    assyrian_monumental_images_carry_legends⟩

theorem assyrian_inherits_geography_reserve :
    GanEdenKarduniyasGeographyReserveWitness.edenIdentificationHeldUnderReserve
      GanEdenKarduniyasGeographyReserveWitness.missingGardenProofReserve ∧
    sealsPreserveLegendContinuity sealContinuityLedger := by
  exact ⟨GanEdenKarduniyasGeographyReserveWitness.gan_eden_identification_held_under_reserve,
    assyrian_seals_preserve_legend_continuity⟩

theorem assyrian_monumental_continuity_witness :
    oralToMonumentalCarrierShift monumentalEraTransition ∧
    sealsPreserveLegendContinuity sealContinuityLedger ∧
    knowledgeSurvivesEvidenceGap interveningTransmissionBridge ∧
    monumentalImagesCarryLegends assyrianRevivalImageProgram ∧
    artLedgerExtendsTextWitness artContinuityMethod ∧
    Gnosis.ConversationalProsody.prosodyReadyToClose
      Gnosis.ConversationalProsody.canonicalConversationalGate
      assyrianContinuityReserveSignal = false ∧
    Gnosis.ThothConversationAntiQueue.heldOpen
      assyrianContinuityAntiQueueState := by
  exact ⟨assyrian_oral_to_monumental_carrier_shift,
    assyrian_seals_preserve_legend_continuity,
    assyrian_knowledge_survives_evidence_gap,
    assyrian_monumental_images_carry_legends,
    assyrian_art_ledger_extends_text_witness,
    assyrian_continuity_reserve_signal_not_ready,
    assyrian_continuity_reserve_keeps_antiqueue_open⟩

end AssyrianMonumentalContinuityWitness
end Gnosis.Witnesses.Chaldean
