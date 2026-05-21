import Gnosis.Witnesses.Chaldean.HumbabaForestGateTempestWitness
import Gnosis.Witnesses.Chaldean.IshtarSevenGateRegaliaBodyWitness

namespace Gnosis.Witnesses.Chaldean
namespace IshtarCaptureBargainBullRetaliationWitness

/-!
# Ishtar Capture-Bargain Bull-Retaliation Witness

Source surface:
`docs/ebooks/source-texts/chaldean-account-of-genesis-smith.txt`, Chapter XIV,
Ishtar's marriage offer, Izdubar's refusal, and the divine bull episode.

The passage is a capture-bargain counterproof. Ishtar offers oath, marriage,
chariot, conquest, tribute, fertility, and rule. Izdubar refuses by citing her
history of consuming or degrading prior partners: Dumuzi mourned, eagle wings
broken, lion claws drawn out by sevens, horse love exhausted, ruler made
leopard, husbandman struck and fixed. The rejected bargain escalates into a
weapon request: a divine bull. After the bull is slain, Ishtar curses from the
wall, Heabani throws back the bull-member as counter-curse, the horns are
dedicated, hands are washed in Euphrates, and the city is circled in public
proclamation.

No `sorry`, no new `axiom`.
-/

structure CaptureBargainOffer where
  oathAsBond : Bool := true
  marriageAsCapture : Bool := true
  goldChariotOffered : Bool := true
  conquestDaysOffered : Bool := true
  kingsLordsPrincesUnderRule : Bool := true
  tributeAndFertilityOffered : Bool := true
deriving DecidableEq, Repr

def captureBargainOffer : CaptureBargainOffer := {}

def ishtarCaptureBargain (c : CaptureBargainOffer) : Prop :=
  c.oathAsBond = true ∧
  c.marriageAsCapture = true ∧
  c.goldChariotOffered = true ∧
  c.conquestDaysOffered = true ∧
  c.kingsLordsPrincesUnderRule = true ∧
  c.tributeAndFertilityOffered = true

structure PriorPartnerDamageLedger where
  dumuziMourningNamed : Bool := true
  eagleWingsBroken : Bool := true
  lionClawsDrawnBySevens : Bool := true
  horseLoveExhaustedAfterSevenKaspu : Bool := true
  rulerChangedToLeopard : Bool := true
  husbandmanFixedUnableToRise : Bool := true
deriving DecidableEq, Repr

def priorPartnerDamageLedger : PriorPartnerDamageLedger := {}

def damagedPartnersProveCaptureRisk (p : PriorPartnerDamageLedger) : Prop :=
  p.dumuziMourningNamed = true ∧
  p.eagleWingsBroken = true ∧
  p.lionClawsDrawnBySevens = true ∧
  p.horseLoveExhaustedAfterSevenKaspu = true ∧
  p.rulerChangedToLeopard = true ∧
  p.husbandmanFixedUnableToRise = true

structure BullRetaliationEscalation where
  ishtarAscendsToAnuInAnger : Bool := true
  divineBullRequested : Bool := true
  warriorsFallInBullCrisis : Bool := true
  heabaniAndIzdubarCoordinate : Bool := true
  divineBullSlain : Bool := true
deriving DecidableEq, Repr

def bullRetaliationEscalation : BullRetaliationEscalation := {}

def rejectedCaptureEscalatesToBull (b : BullRetaliationEscalation) : Prop :=
  b.ishtarAscendsToAnuInAnger = true ∧
  b.divineBullRequested = true ∧
  b.warriorsFallInBullCrisis = true ∧
  b.heabaniAndIzdubarCoordinate = true ∧
  b.divineBullSlain = true

structure PublicCounterCurseResolution where
  ishtarCursesFromWall : Bool := true
  heabaniThrowsBullMember : Bool := true
  curseTurnedAgainstHerSide : Bool := true
  hornsDedicatedToGod : Bool := true
  handsWashedInEuphrates : Bool := true
  cityCircledAndProclaimed : Bool := true
deriving DecidableEq, Repr

def publicCounterCurseResolution : PublicCounterCurseResolution := {}

def publicCounterCurseRepair (p : PublicCounterCurseResolution) : Prop :=
  p.ishtarCursesFromWall = true ∧
  p.heabaniThrowsBullMember = true ∧
  p.curseTurnedAgainstHerSide = true ∧
  p.hornsDedicatedToGod = true ∧
  p.handsWashedInEuphrates = true ∧
  p.cityCircledAndProclaimed = true

theorem ishtar_capture_bargain :
    ishtarCaptureBargain captureBargainOffer := by
  unfold ishtarCaptureBargain captureBargainOffer
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem ishtar_damaged_partners_prove_capture_risk :
    damagedPartnersProveCaptureRisk priorPartnerDamageLedger := by
  unfold damagedPartnersProveCaptureRisk priorPartnerDamageLedger
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem ishtar_rejected_capture_escalates_to_bull :
    rejectedCaptureEscalatesToBull bullRetaliationEscalation := by
  unfold rejectedCaptureEscalatesToBull bullRetaliationEscalation
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem ishtar_public_counter_curse_repair :
    publicCounterCurseRepair publicCounterCurseResolution := by
  unfold publicCounterCurseRepair publicCounterCurseResolution
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem ishtar_inherits_gate_body_capture_context :
    IshtarSevenGateRegaliaBodyWitness.gateIndexedBodyLedger
      IshtarSevenGateRegaliaBodyWitness.bodyLedgerGateProtocol ∧
    damagedPartnersProveCaptureRisk priorPartnerDamageLedger := by
  exact ⟨IshtarSevenGateRegaliaBodyWitness.ishtar_gate_indexed_body_ledger,
    ishtar_damaged_partners_prove_capture_risk⟩

theorem ishtar_inherits_humbaba_public_freedom_context :
    HumbabaForestGateTempestWitness.tyrantBoundaryConvertsToFreedom
      HumbabaForestGateTempestWitness.oppressorBoundaryConversion ∧
    publicCounterCurseRepair publicCounterCurseResolution := by
  exact ⟨HumbabaForestGateTempestWitness.humbaba_tyrant_boundary_converts_to_freedom,
    ishtar_public_counter_curse_repair⟩

theorem ishtar_capture_bargain_bull_retaliation_witness :
    ishtarCaptureBargain captureBargainOffer ∧
    damagedPartnersProveCaptureRisk priorPartnerDamageLedger ∧
    rejectedCaptureEscalatesToBull bullRetaliationEscalation ∧
    publicCounterCurseRepair publicCounterCurseResolution := by
  exact ⟨ishtar_capture_bargain,
    ishtar_damaged_partners_prove_capture_risk,
    ishtar_rejected_capture_escalates_to_bull,
    ishtar_public_counter_curse_repair⟩

end IshtarCaptureBargainBullRetaliationWitness
end Gnosis.Witnesses.Chaldean
