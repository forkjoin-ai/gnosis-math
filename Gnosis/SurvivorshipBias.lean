import Init
import Gnosis.Bridges.SimpsonSurvivorshipQueueBridge

/-!
# SurvivorshipBias

Finite Wald bomber armor witness.

The observed data are the planes that returned. The critical data are the
planes that did not return. The wrong rule armors the most visible hits on
survivors; Wald's correction armors the missing-hit regions because hits there
select planes out of the observed sample.
-/

namespace SurvivorshipBias

/-- Bomber regions relevant to the classical survivorship-bias example. -/
inductive BomberRegion where
  | wings
  | fuselage
  | tail
  | engines
  | cockpit
  | fuelTanks
deriving DecidableEq, Repr

/-- Region-level counts: visible hits among returned planes and missing losses. -/
structure RegionObservation where
  returnedHits : Nat
  missingLosses : Nat
deriving DecidableEq, Repr

/-- Classical Wald data sketch: visible holes are not where loss occurs. -/
def waldObservation : BomberRegion → RegionObservation
  | .wings => { returnedHits := 9, missingLosses := 0 }
  | .fuselage => { returnedHits := 7, missingLosses := 0 }
  | .tail => { returnedHits := 6, missingLosses := 0 }
  | .engines => { returnedHits := 0, missingLosses := 9 }
  | .cockpit => { returnedHits := 0, missingLosses := 7 }
  | .fuelTanks => { returnedHits := 0, missingLosses := 6 }

/-- The naive rule armors where survivor hit-counts are visible. -/
def naiveArmorTarget (region : BomberRegion) : Bool :=
  decide (0 < (waldObservation region).returnedHits)

/-- Wald's rule armors where returned planes show no holes but losses appear. -/
def waldArmorTarget (region : BomberRegion) : Bool :=
  decide ((waldObservation region).returnedHits = 0 ∧
    0 < (waldObservation region).missingLosses)

/-- Survivorship selection hides a region when losses are positive but survivors show no hits. -/
def selectionHidesRegion (region : BomberRegion) : Prop :=
  (waldObservation region).returnedHits = 0 ∧
    0 < (waldObservation region).missingLosses

/-- The naive rule armors wings. -/
theorem naive_armors_wings :
    naiveArmorTarget .wings = true := by
  native_decide

/-- The naive rule armors fuselage. -/
theorem naive_armors_fuselage :
    naiveArmorTarget .fuselage = true := by
  native_decide

/-- The naive rule armors tail. -/
theorem naive_armors_tail :
    naiveArmorTarget .tail = true := by
  native_decide

/-- The naive rule misses engines, the first Wald-critical target. -/
theorem naive_misses_engines :
    naiveArmorTarget .engines = false := by
  native_decide

/-- The naive rule misses cockpit, another Wald-critical target. -/
theorem naive_misses_cockpit :
    naiveArmorTarget .cockpit = false := by
  native_decide

/-- The naive rule misses fuel tanks, another Wald-critical target. -/
theorem naive_misses_fuel_tanks :
    naiveArmorTarget .fuelTanks = false := by
  native_decide

/-- Wald's rule targets engines. -/
theorem wald_armors_engines :
    waldArmorTarget .engines = true := by
  native_decide

/-- Wald's rule targets cockpit. -/
theorem wald_armors_cockpit :
    waldArmorTarget .cockpit = true := by
  native_decide

/-- Wald's rule targets fuel tanks. -/
theorem wald_armors_fuel_tanks :
    waldArmorTarget .fuelTanks = true := by
  native_decide

/-- Wald's rule does not target the visible survivor-hit regions. -/
theorem wald_does_not_armor_visible_survivor_regions :
    waldArmorTarget .wings = false ∧
    waldArmorTarget .fuselage = false ∧
    waldArmorTarget .tail = false := by
  native_decide

/-- Every Wald target is exactly a region hidden by survivorship selection. -/
theorem wald_target_iff_selection_hides_region
    (region : BomberRegion) :
    waldArmorTarget region = true ↔ selectionHidesRegion region := by
  unfold waldArmorTarget selectionHidesRegion
  constructor
  · intro h
    exact of_decide_eq_true h
  · intro h
    exact decide_eq_true h

/--
The naive conclusion and Wald's conclusion are disjoint on all regions: a
visible survivor-hit region is not a missing-loss region in this witness.
-/
theorem naive_and_wald_targets_are_disjoint
    (region : BomberRegion) :
    ¬ (naiveArmorTarget region = true ∧ waldArmorTarget region = true) := by
  cases region <;> native_decide

/-- The three critical missing-hole regions are exactly the Wald armor set. -/
theorem wald_missing_holes_master :
    waldArmorTarget .engines = true ∧
    waldArmorTarget .cockpit = true ∧
    waldArmorTarget .fuelTanks = true ∧
    naiveArmorTarget .engines = false ∧
    naiveArmorTarget .cockpit = false ∧
    naiveArmorTarget .fuelTanks = false := by
  native_decide

/-- Survivorship mortality budget reads the missing-loss count. -/
def mortalityScenarioOfRegion
    (region : BomberRegion) :
    SimpsonSurvivorshipQueueBridge.MortalityScenario :=
  { R := (waldObservation region).returnedHits +
      (waldObservation region).missingLosses,
    v := (waldObservation region).missingLosses,
    hBound := by
      exact Nat.le_add_left
        (waldObservation region).missingLosses
        (waldObservation region).returnedHits }

/-- The queue bridge budget for a region is its missing-loss count. -/
theorem mortality_budget_of_region_is_missing_losses
    (region : BomberRegion) :
    SimpsonSurvivorshipQueueBridge.survivorshipMortalityBudget
      (mortalityScenarioOfRegion region) =
        (waldObservation region).missingLosses := by
  rfl

/-- Wald's engine target yields the existing survivorship queue boundary. -/
theorem wald_engine_target_yields_survivorship_queue_boundary :
    SimpsonSurvivorshipQueueBridge.survivorshipMortalityBudget
      (mortalityScenarioOfRegion .engines) = 9 ∧
    ∃ boundary : SimpsonSurvivorshipQueueBridge.QueueBoundaryWitnessNat,
      boundary.beta1 = 0 ∧
      boundary.capacity = 1 ∧
      boundary.arrivalRate =
        SimpsonSurvivorshipQueueBridge.survivorshipMortalityBudget
          (mortalityScenarioOfRegion .engines) := by
  have hBridge :=
    SimpsonSurvivorshipQueueBridge.survivorship_mortality_yields_unit_queue_boundary
      (mortalityScenarioOfRegion .engines)
  exact ⟨rfl,
    ⟨hBridge.right.choose,
      hBridge.right.choose_spec.left,
      hBridge.right.choose_spec.right.left,
      hBridge.right.choose_spec.right.right.left⟩⟩

end SurvivorshipBias
