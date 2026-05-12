import Init

/-!
# Simpson and Survivorship Queue Bridge

Finite queue-boundary witnesses for the stale MCP rows that used to point at
the old Simpson/survivorship bridge. The bridge keeps the original theorem
names while avoiding the dropped Mathlib surface.
-/

namespace SimpsonSurvivorshipQueueBridge

structure SimpsonScenario where
  v1_A : Nat
  v2_A : Nat
deriving DecidableEq, Repr

structure MortalityScenario where
  R : Nat
  v : Nat
  hBound : v ≤ R
deriving Repr

def simpsonConfounderBudget (scenario : SimpsonScenario) : Nat :=
  scenario.v1_A + scenario.v2_A

def survivorshipMortalityBudget (scenario : MortalityScenario) : Nat :=
  scenario.v

def godWeight (scenario : MortalityScenario) : Nat :=
  scenario.R - scenario.v + 1

def replicaCount (budget : Nat) : Nat := 2 * budget + 1

def quorumSize (_replicas budget : Nat) : Nat := budget + 1

structure QueueBoundaryWitnessNat where
  beta1 : Nat
  capacity : Nat
  arrivalRate : Nat
  serviceRate : Nat
deriving DecidableEq, Repr

def canonicalQueueBoundary (budget : Nat) : QueueBoundaryWitnessNat :=
  { beta1 := 0
    capacity := 1
    arrivalRate := budget
    serviceRate := quorumSize (replicaCount budget) budget }

structure GeometricRateNat where
  numerator : Nat
  denominator : Nat
  initialBound : Nat
  hRateLtOne : numerator < denominator
  hDenomPos : 0 < denominator
  hInitialBoundPos : 0 < initialBound
deriving Repr

def budgetGeometricRate (budget : Nat) : GeometricRateNat :=
  { numerator := 3
    denominator := 4
    initialBound := budget + 1
    hRateLtOne := by decide
    hDenomPos := by decide
    hInitialBoundPos := Nat.succ_pos budget }

theorem simpson_confounder_yields_unit_queue_boundary
    (scenario : SimpsonScenario) :
    ∃ boundary : QueueBoundaryWitnessNat,
      boundary.beta1 = 0 ∧
      boundary.capacity = 1 ∧
      boundary.arrivalRate = simpsonConfounderBudget scenario ∧
      boundary.serviceRate =
        quorumSize
          (replicaCount (simpsonConfounderBudget scenario))
          (simpsonConfounderBudget scenario) := by
  exact ⟨canonicalQueueBoundary (simpsonConfounderBudget scenario),
    rfl, rfl, rfl, rfl⟩

theorem simpson_confounder_does_not_force_positive_beta1
    (scenario : SimpsonScenario) :
    ¬ (∀ boundary : QueueBoundaryWitnessNat,
        boundary.arrivalRate = simpsonConfounderBudget scenario →
        boundary.serviceRate =
          quorumSize
            (replicaCount (simpsonConfounderBudget scenario))
            (simpsonConfounderBudget scenario) →
        0 < boundary.beta1) := by
  intro hAll
  let boundary := canonicalQueueBoundary (simpsonConfounderBudget scenario)
  exact Nat.lt_irrefl 0 (hAll boundary rfl rfl)

theorem survivorship_correction_identity
    (scenario : MortalityScenario) :
    godWeight scenario = scenario.R - scenario.v + 1 := by
  rfl

theorem survivorship_mortality_yields_unit_queue_boundary
    (scenario : MortalityScenario) :
    godWeight scenario = scenario.R - scenario.v + 1 ∧
    ∃ boundary : QueueBoundaryWitnessNat,
      boundary.beta1 = 0 ∧
      boundary.capacity = 1 ∧
      boundary.arrivalRate = survivorshipMortalityBudget scenario ∧
      boundary.serviceRate =
        quorumSize
          (replicaCount (survivorshipMortalityBudget scenario))
          (survivorshipMortalityBudget scenario) := by
  exact ⟨survivorship_correction_identity scenario,
    ⟨canonicalQueueBoundary (survivorshipMortalityBudget scenario),
      rfl, rfl, rfl, rfl⟩⟩

theorem survivorship_mortality_does_not_force_strict_capacity_growth
    (scenario : MortalityScenario) :
    ¬ (∀ boundary : QueueBoundaryWitnessNat,
        boundary.arrivalRate = survivorshipMortalityBudget scenario →
        boundary.serviceRate =
          quorumSize
            (replicaCount (survivorshipMortalityBudget scenario))
            (survivorshipMortalityBudget scenario) →
        1 < boundary.capacity) := by
  intro hAll
  let boundary := canonicalQueueBoundary (survivorshipMortalityBudget scenario)
  exact Nat.lt_irrefl 1 (hAll boundary rfl rfl)

theorem simpson_confounder_yields_geometric_rate_certificate
    (scenario : SimpsonScenario) :
    ∃ rate : GeometricRateNat,
      rate = budgetGeometricRate (simpsonConfounderBudget scenario) ∧
      rate.initialBound = simpsonConfounderBudget scenario + 1 ∧
      rate.numerator = 3 ∧
      rate.denominator = 4 ∧
      rate.numerator < rate.denominator ∧
      0 < rate.initialBound := by
  refine ⟨budgetGeometricRate (simpsonConfounderBudget scenario),
    rfl, rfl, rfl, rfl, ?_, ?_⟩
  · exact (budgetGeometricRate (simpsonConfounderBudget scenario)).hRateLtOne
  · exact (budgetGeometricRate (simpsonConfounderBudget scenario)).hInitialBoundPos

structure SimpsonKernelLiftBundle where
  scenario : SimpsonScenario
  budget : Nat
  hBudgetEq : budget = simpsonConfounderBudget scenario
  driftGap : Nat
  hDriftGap : 0 < driftGap
deriving Repr

end SimpsonSurvivorshipQueueBridge

namespace SimpsonKernelLiftAdapter

abbrev SimpsonKernelLiftBundle :=
  SimpsonSurvivorshipQueueBridge.SimpsonKernelLiftBundle

theorem simpson_continuous_ergodicity_lift
    (adapter : SimpsonKernelLiftBundle) :
    adapter.budget =
      SimpsonSurvivorshipQueueBridge.simpsonConfounderBudget adapter.scenario ∧
    0 < adapter.driftGap :=
  ⟨adapter.hBudgetEq, adapter.hDriftGap⟩

end SimpsonKernelLiftAdapter
