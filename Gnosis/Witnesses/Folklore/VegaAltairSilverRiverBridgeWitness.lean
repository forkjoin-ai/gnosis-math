import Gnosis.Witnesses.Folklore.ZodiacGateProfileSeedWitness

namespace Gnosis.Witnesses.Folklore
namespace VegaAltairSilverRiverBridgeWitness

/-!
# Vega-Altair Silver River Bridge Witness

East Asian Qixi / Tanabata folklore gives a sky topology different from the
Orion/Scorpius horizon opposition.

Orion and Scorpius encode anti-coincidence: one rises as the other sets, so the
gate is a horizon separator. Vega and Altair encode a reparable separation:
the Weaver Girl and Cowherd are held apart by the Milky Way / Silver River, but
the seventh day of the seventh lunar month opens a brief bridge. The bridge is
not a permanent merger; it is scheduled crossing under ritual calendar control.

This matters because the separator is not the Earth's horizon but the galactic
river itself. The folklore stores a different gate profile: duty breach,
banishment to opposite banks, annual bridge construction, brief reunion, and
return to separated state.

No `sorry`, no new `axiom`.
-/

structure SilverRiverSeparator where
  vegaWeaverGirl : Bool := true
  altairCowherd : Bool := true
  separatedByMilkyWay : Bool := true
  separatorNamedAsSilverRiver : Bool := true
  boundaryIsGalacticNotHorizon : Bool := true
deriving DecidableEq, Repr

def silverRiverSeparator : SilverRiverSeparator := {}

def silverRiverSeparatesLovers (s : SilverRiverSeparator) : Prop :=
  s.vegaWeaverGirl = true ∧
  s.altairCowherd = true ∧
  s.separatedByMilkyWay = true ∧
  s.separatorNamedAsSilverRiver = true ∧
  s.boundaryIsGalacticNotHorizon = true

structure DutyBreachBanishment where
  romanceDistractsFromDuties : Bool := true
  loversBanishedToOppositeSides : Bool := true
  separationIsPenaltyNotCombat : Bool := true
  workRhythmRestoredByBoundary : Bool := true
deriving DecidableEq, Repr

def dutyBreachBanishment : DutyBreachBanishment := {}

def boundaryRestoresDutyRhythm (d : DutyBreachBanishment) : Prop :=
  d.romanceDistractsFromDuties = true ∧
  d.loversBanishedToOppositeSides = true ∧
  d.separationIsPenaltyNotCombat = true ∧
  d.workRhythmRestoredByBoundary = true

structure MagpieBridgeReunion where
  seventhDaySeventhMonth : Bool := true
  annualPermissionWindow : Bool := true
  magpiesFormBridge : Bool := true
  galacticRiverTemporarilyCrossed : Bool := true
  reunionIsBrief : Bool := true
  separationReturnsAfterWindow : Bool := true
deriving DecidableEq, Repr

def magpieBridgeReunion : MagpieBridgeReunion := {}

def scheduledBridgeRepairsSeparation
    (m : MagpieBridgeReunion) : Prop :=
  m.seventhDaySeventhMonth = true ∧
  m.annualPermissionWindow = true ∧
  m.magpiesFormBridge = true ∧
  m.galacticRiverTemporarilyCrossed = true ∧
  m.reunionIsBrief = true ∧
  m.separationReturnsAfterWindow = true

structure HorizonVersusRiverGate where
  orionScorpiusHorizonOpposition : Bool := true
  vegaAltairRiverSeparation : Bool := true
  horizonGatePreventsMeeting : Bool := true
  riverGateAllowsScheduledBridge : Bool := true
  bothAreSkyTopologyNotSameMyth : Bool := true
deriving DecidableEq, Repr

def horizonVersusRiverGate : HorizonVersusRiverGate := {}

def distinguishesHorizonFromRiverGate
    (h : HorizonVersusRiverGate) : Prop :=
  h.orionScorpiusHorizonOpposition = true ∧
  h.vegaAltairRiverSeparation = true ∧
  h.horizonGatePreventsMeeting = true ∧
  h.riverGateAllowsScheduledBridge = true ∧
  h.bothAreSkyTopologyNotSameMyth = true

theorem silver_river_separates_lovers :
    silverRiverSeparatesLovers silverRiverSeparator := by
  unfold silverRiverSeparatesLovers silverRiverSeparator
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem boundary_restores_duty_rhythm :
    boundaryRestoresDutyRhythm dutyBreachBanishment := by
  unfold boundaryRestoresDutyRhythm dutyBreachBanishment
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem magpie_bridge_schedules_reunion :
    scheduledBridgeRepairsSeparation magpieBridgeReunion := by
  unfold scheduledBridgeRepairsSeparation magpieBridgeReunion
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem horizon_and_river_gates_are_distinct :
    distinguishesHorizonFromRiverGate horizonVersusRiverGate := by
  unfold distinguishesHorizonFromRiverGate horizonVersusRiverGate
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem silver_river_extends_sky_gate_program :
    ZodiacGateProfileSeedWitness.comparativeSkyCarriersUnderReserve
      ZodiacGateProfileSeedWitness.comparativeSkyCarriers ∧
    silverRiverSeparatesLovers silverRiverSeparator ∧
    scheduledBridgeRepairsSeparation magpieBridgeReunion ∧
    distinguishesHorizonFromRiverGate horizonVersusRiverGate := by
  exact ⟨ZodiacGateProfileSeedWitness.comparative_sky_carriers_under_reserve,
    silver_river_separates_lovers,
    magpie_bridge_schedules_reunion,
    horizon_and_river_gates_are_distinct⟩

theorem vega_altair_silver_river_bridge_witness :
    silverRiverSeparatesLovers silverRiverSeparator ∧
    boundaryRestoresDutyRhythm dutyBreachBanishment ∧
    scheduledBridgeRepairsSeparation magpieBridgeReunion ∧
    distinguishesHorizonFromRiverGate horizonVersusRiverGate := by
  exact ⟨silver_river_separates_lovers,
    boundary_restores_duty_rhythm,
    magpie_bridge_schedules_reunion,
    horizon_and_river_gates_are_distinct⟩

end VegaAltairSilverRiverBridgeWitness
end Gnosis.Witnesses.Folklore
