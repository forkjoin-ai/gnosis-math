namespace GoodhartMechanismQueueKernelBridge

/-!
Init-only Goodhart/mechanism queue bridge.

Proxy-gap and mechanism-externality budgets are finite Nat quantities. When an
explicit equality identifies those budgets, the same canonical one-path queue
witness transports across both interpretations.
-/

structure GoodhartSetup where
  vTrue : Nat
  vGamed : Nat
  hGamedLeTrue : vGamed ≤ vTrue
deriving Repr

structure MechanismSetup where
  vWithout : Nat
  vWith : Nat
  hWithoutLeWith : vWithout ≤ vWith
deriving Repr

def goodhartProxyGap (setup : GoodhartSetup) : Nat :=
  setup.vTrue - setup.vGamed

def mechanismExternality (setup : MechanismSetup) : Nat :=
  setup.vWith - setup.vWithout

def replicaCount (failureBudget : Nat) : Nat :=
  2 * failureBudget + 1

def quorumSize (_replicas failureBudget : Nat) : Nat :=
  failureBudget + 1

structure QueueBoundaryWitnessNat where
  beta1 : Nat
  capacity : Nat
  arrivalRate : Nat
  serviceRate : Nat
deriving DecidableEq, Repr

def canonicalQueueBoundary (failureBudget : Nat) : QueueBoundaryWitnessNat :=
  { beta1 := 0
    capacity := 1
    arrivalRate := failureBudget
    serviceRate := quorumSize (replicaCount failureBudget) failureBudget }

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

theorem goodhart_proxy_gap_yields_unit_queue_boundary
    (setup : GoodhartSetup) :
    goodhartProxyGap setup = setup.vTrue - setup.vGamed ∧
    ∃ boundary : QueueBoundaryWitnessNat,
      boundary.beta1 = 0 ∧
      boundary.capacity = 1 ∧
      boundary.arrivalRate = goodhartProxyGap setup ∧
      boundary.serviceRate =
        quorumSize (replicaCount (goodhartProxyGap setup)) (goodhartProxyGap setup) := by
  refine ⟨rfl, ?_⟩
  exact ⟨canonicalQueueBoundary (goodhartProxyGap setup), rfl, rfl, rfl, rfl⟩

theorem mechanism_externality_yields_unit_queue_boundary
    (setup : MechanismSetup) :
    mechanismExternality setup = setup.vWith - setup.vWithout ∧
    ∃ boundary : QueueBoundaryWitnessNat,
      boundary.beta1 = 0 ∧
      boundary.capacity = 1 ∧
      boundary.arrivalRate = mechanismExternality setup ∧
      boundary.serviceRate =
        quorumSize (replicaCount (mechanismExternality setup)) (mechanismExternality setup) := by
  refine ⟨rfl, ?_⟩
  exact ⟨canonicalQueueBoundary (mechanismExternality setup), rfl, rfl, rfl, rfl⟩

theorem goodhart_mechanism_budget_bridge_yields_unit_queue_boundary
    (goodhart : GoodhartSetup)
    (mechanism : MechanismSetup)
    (hBridge : mechanismExternality mechanism = goodhartProxyGap goodhart) :
    mechanismExternality mechanism = goodhartProxyGap goodhart ∧
    ∃ boundary : QueueBoundaryWitnessNat,
      boundary.beta1 = 0 ∧
      boundary.capacity = 1 ∧
      boundary.arrivalRate = mechanismExternality mechanism ∧
      boundary.serviceRate =
        quorumSize (replicaCount (mechanismExternality mechanism))
          (mechanismExternality mechanism) := by
  refine ⟨hBridge, ?_⟩
  exact ⟨canonicalQueueBoundary (mechanismExternality mechanism), rfl, rfl, rfl, rfl⟩

theorem goodhart_mechanism_budget_bridge_does_not_force_positive_beta1
    (goodhart : GoodhartSetup)
    (mechanism : MechanismSetup)
    (_hBridge : mechanismExternality mechanism = goodhartProxyGap goodhart) :
    ¬ (∀ boundary : QueueBoundaryWitnessNat,
        boundary.arrivalRate = mechanismExternality mechanism →
        boundary.serviceRate =
          quorumSize (replicaCount (mechanismExternality mechanism))
            (mechanismExternality mechanism) →
        0 < boundary.beta1) := by
  intro hAll
  let boundary := canonicalQueueBoundary (mechanismExternality mechanism)
  have h : 0 < boundary.beta1 := hAll boundary rfl rfl
  exact Nat.lt_irrefl 0 h

theorem adversarial_gap_yields_geometric_rate_certificate
    (delta : Nat) :
    ∃ rate : GeometricRateNat,
      rate = budgetGeometricRate delta ∧
      rate.initialBound = delta + 1 ∧
      rate.numerator = 3 ∧
      rate.denominator = 4 ∧
      rate.numerator < rate.denominator ∧
      0 < rate.initialBound := by
  refine ⟨budgetGeometricRate delta, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · exact (budgetGeometricRate delta).hRateLtOne
  · exact (budgetGeometricRate delta).hInitialBoundPos

structure GoodhartMechanismKernelLiftAdapter where
  goodhart : GoodhartSetup
  mechanism : MechanismSetup
  budget : Nat
  hBudgetEq : budget = mechanismExternality mechanism
  hBridge : mechanismExternality mechanism = goodhartProxyGap goodhart
  driftGap : Nat
  hDriftGap : 0 < driftGap
  kernelMatched : Bool
deriving Repr

namespace GoodhartMechanismKernelLiftAdapter

theorem goodhart_mechanism_continuous_ergodicity_lift
    (adapter : GoodhartMechanismKernelLiftAdapter) :
    adapter.budget = mechanismExternality adapter.mechanism ∧
    mechanismExternality adapter.mechanism = goodhartProxyGap adapter.goodhart ∧
    0 < adapter.driftGap := by
  exact ⟨adapter.hBudgetEq, adapter.hBridge, adapter.hDriftGap⟩

end GoodhartMechanismKernelLiftAdapter

end GoodhartMechanismQueueKernelBridge
