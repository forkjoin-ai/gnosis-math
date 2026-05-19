import Gnosis.SpectralNoiseEquilibrium
import Gnosis.TwoTypesOfSin
import Gnosis.WarmupController

namespace Gnosis
namespace DaedalusIcarusWitness

open SpectralNoiseEquilibrium

/-!
# Daedalus / Icarus Witness

This module formalizes Daedalus and Icarus as a finite operational-boundary
and thermodynamic-limit witness.

Reading:

- The Labyrinth is an oracle stall whose load can be observed and preserved.
- Wax wings are a carrier with a safe altitude corridor.
- Too low accumulates under-deficit drag; too high crosses the repair redline.
- Icarus chooses the high unsafe path and sheds load.
- Daedalus stays in the midrange fixed corridor and survives.
-/

/-- The Labyrinth as a bounded stall with a known exit protocol. -/
structure LabyrinthStall where
  constraintLoad : Nat
  exitProtocolKnown : Bool
deriving Repr, DecidableEq

def daedalusLabyrinth : LabyrinthStall :=
  { constraintLoad := 7, exitProtocolKnown := true }

def stallLoadObserved (n : Nat) : Nat := n + 0

def stallAnnihilated (l : LabyrinthStall) : Prop :=
  l.exitProtocolKnown = true ∧ stallLoadObserved l.constraintLoad = l.constraintLoad

/-- Wax wings as a finite carrier. -/
structure WingCarrier where
  liftCapacity : Nat
  waxMeltPoint : Nat
  sprayTolerance : Nat
deriving Repr, DecidableEq

def waxWings : WingCarrier :=
  { liftCapacity := 10, waxMeltPoint := 8, sprayTolerance := 2 }

/-- The safe corridor between sea drag and solar heat. -/
structure FlightPath where
  altitude : Nat
  seaSpray : Nat
  sunHeat : Nat
deriving Repr, DecidableEq

def daedalusPath : FlightPath :=
  { altitude := 5, seaSpray := 1, sunHeat := 5 }

def lowPath : FlightPath :=
  { altitude := 1, seaSpray := 4, sunHeat := 2 }

def icarusPath : FlightPath :=
  { altitude := 9, seaSpray := 0, sunHeat := 12 }

def withinFlightCorridor (w : WingCarrier) (p : FlightPath) : Prop :=
  p.seaSpray ≤ w.sprayTolerance ∧ p.sunHeat < w.waxMeltPoint

def lowBoundaryDebt (w : WingCarrier) (p : FlightPath) : Nat :=
  p.seaSpray - w.sprayTolerance

def highBoundaryDebt (w : WingCarrier) (p : FlightPath) : Nat :=
  p.sunHeat - w.waxMeltPoint

def compressionFailure (w : WingCarrier) (p : FlightPath) : Prop :=
  w.waxMeltPoint < p.sunHeat

/-- The heat face paid by the wax binder once the sun signal dominates. -/
def waxHeatCost : BuleyUnit :=
  { waste := 4, opportunity := 1, diversity := 1 }

def daedalusAction : WarmupControllerAction :=
  chooseWarmupAction 1 0 1 0 4 2 20

def icarusAction : WarmupControllerAction :=
  chooseWarmupAction 10 0 10 0 4 2 1

def lowAction : WarmupControllerAction :=
  chooseWarmupAction 10 0 10 3 0 2 1

def survivesFlight (w : WingCarrier) (p : FlightPath) : Prop :=
  withinFlightCorridor w p

def fallsToVacuum (action : WarmupControllerAction) : Prop :=
  action = .shedLoad

def mdlWeight (budget cost : Nat) : Nat :=
  budget - Nat.min cost budget + 1

/-- Icarus confuses agent sensation with the carrier/position boundary. -/
def icarusAgentPositionCollapse : Prop :=
  TwoTypesOfSin.isASin TwoTypesOfSin.animalMagnetism = true

theorem labyrinth_stall_annihilated :
    stallAnnihilated daedalusLabyrinth := by
  unfold stallAnnihilated daedalusLabyrinth
  exact ⟨rfl, by unfold stallLoadObserved; rfl⟩

theorem daedalus_stays_inside_corridor :
    survivesFlight waxWings daedalusPath := by
  unfold survivesFlight withinFlightCorridor waxWings daedalusPath
  exact ⟨by decide, by decide⟩

theorem low_path_accumulates_drag_debt :
    0 < lowBoundaryDebt waxWings lowPath := by
  unfold lowBoundaryDebt waxWings lowPath
  decide

theorem icarus_crosses_high_boundary :
    compressionFailure waxWings icarusPath := by
  unfold compressionFailure waxWings icarusPath
  decide

theorem wax_heat_cost_positive :
    0 < buleyUnitScore waxHeatCost := by
  unfold waxHeatCost buleyUnitScore
  decide

theorem daedalus_constrains_within_redline :
    daedalusAction = .constrain := by
  unfold daedalusAction
  exact choose_constrain_below_redline
    (hUnder := rfl)
    (hOver := by decide)
    (hDeficitWeight := by decide)
    (hBelow := by decide)

theorem icarus_sheds_load_above_redline :
    icarusAction = .shedLoad := by
  unfold icarusAction
  exact choose_shed_load_when_over_above_redline
    (hUnder := rfl)
    (hOver := by decide)
    (hDeficitWeight := by decide)
    (hAbove := by decide)

theorem low_path_sheds_load_above_redline :
    lowAction = .shedLoad := by
  unfold lowAction
  exact choose_shed_load_when_under_above_redline
    (hUnder := by decide)
    (hOver := rfl)
    (hDeficitWeight := by decide)
    (hAbove := by decide)

theorem icarus_falls_to_vacuum :
    fallsToVacuum icarusAction := by
  unfold fallsToVacuum
  exact icarus_sheds_load_above_redline

theorem daedalus_midrange_is_mdl_optimal :
    mdlWeight 10 5 > mdlWeight 10 9 := by
  unfold mdlWeight
  decide

theorem icarus_agent_position_collapse :
    icarusAgentPositionCollapse :=
  TwoTypesOfSin.animalMagnetism_is_sin

/-- Master witness: the Labyrinth stall is understood, the wax carrier has a
safe corridor, Daedalus stays inside it, and Icarus crosses the high thermal
boundary, triggering shed-load collapse. -/
theorem daedalus_icarus_witness :
    stallAnnihilated daedalusLabyrinth ∧
    survivesFlight waxWings daedalusPath ∧
    0 < lowBoundaryDebt waxWings lowPath ∧
    compressionFailure waxWings icarusPath ∧
    0 < buleyUnitScore waxHeatCost ∧
    daedalusAction = .constrain ∧
    lowAction = .shedLoad ∧
    icarusAction = .shedLoad ∧
    fallsToVacuum icarusAction ∧
    mdlWeight 10 5 > mdlWeight 10 9 ∧
    icarusAgentPositionCollapse := by
  exact ⟨labyrinth_stall_annihilated,
    daedalus_stays_inside_corridor,
    low_path_accumulates_drag_debt,
    icarus_crosses_high_boundary,
    wax_heat_cost_positive,
    daedalus_constrains_within_redline,
    low_path_sheds_load_above_redline,
    icarus_sheds_load_above_redline,
    icarus_falls_to_vacuum,
    daedalus_midrange_is_mdl_optimal,
    icarus_agent_position_collapse⟩

end DaedalusIcarusWitness
end Gnosis
