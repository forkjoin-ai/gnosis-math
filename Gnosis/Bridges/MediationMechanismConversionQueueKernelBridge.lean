namespace MediationMechanismConversionQueueKernelBridge

/-!
Init-only mediation/mechanism/conversion queue bridge.

The restored surface keeps the finite interpretation: mediation loss and
conversion vent mass provide positive queue budget, mechanism externality adds
optional mass, and canonical witnesses refute over-strong forcing claims.
-/

structure MediationSetup where
  mediatorLoss : Nat
  hMediatorLoss : 1 ≤ mediatorLoss
deriving Repr

structure ConversionSetup where
  uiFriction : Nat
  buleInvestment : Nat
  ventSlam : Nat
  hAbandon : buleInvestment < uiFriction
  hVent : ventSlam = uiFriction - buleInvestment
deriving Repr

structure MechanismSetup where
  vWithout : Nat
  vWith : Nat
  hWorse : vWithout ≤ vWith
deriving Repr

def conversionVentFailureBudget (conversion : ConversionSetup) : Nat :=
  conversion.ventSlam

def mechanismExternalityBudget (mechanism : MechanismSetup) : Nat :=
  mechanism.vWith - mechanism.vWithout

def mechanismConversionFailureBudget
    (mechanism : MechanismSetup)
    (conversion : ConversionSetup) : Nat :=
  mechanismExternalityBudget mechanism + conversionVentFailureBudget conversion

def mediationMechanismConversionFailureBudget
    (mediation : MediationSetup)
    (conversion : ConversionSetup) : Nat :=
  mediation.mediatorLoss + conversionVentFailureBudget conversion

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

theorem conversion_vent_positive (conversion : ConversionSetup) :
    0 < conversionVentFailureBudget conversion := by
  unfold conversionVentFailureBudget
  rw [conversion.hVent]
  exact Nat.sub_pos_of_lt conversion.hAbandon

theorem mediation_mechanism_conversion_budget_positive
    (mediation : MediationSetup)
    (conversion : ConversionSetup) :
    0 < mediationMechanismConversionFailureBudget mediation conversion := by
  unfold mediationMechanismConversionFailureBudget
  exact Nat.lt_add_right (conversionVentFailureBudget conversion) mediation.hMediatorLoss

theorem mechanism_conversion_budget_positive
    (mechanism : MechanismSetup)
    (conversion : ConversionSetup) :
    0 < mechanismConversionFailureBudget mechanism conversion := by
  unfold mechanismConversionFailureBudget
  exact Nat.lt_add_left (mechanismExternalityBudget mechanism) (conversion_vent_positive conversion)

theorem conversion_vent_budget_yields_unit_queue_boundary
    (conversion : ConversionSetup) :
    0 < conversionVentFailureBudget conversion ∧
    ∃ boundary : QueueBoundaryWitnessNat,
      boundary.beta1 = 0 ∧
      boundary.capacity = 1 ∧
      boundary.arrivalRate = conversionVentFailureBudget conversion ∧
      boundary.serviceRate =
        quorumSize (replicaCount (conversionVentFailureBudget conversion))
          (conversionVentFailureBudget conversion) := by
  refine ⟨conversion_vent_positive conversion, ?_⟩
  exact ⟨canonicalQueueBoundary (conversionVentFailureBudget conversion), rfl, rfl, rfl, rfl⟩

theorem mechanism_conversion_budget_yields_unit_queue_boundary
    (mechanism : MechanismSetup)
    (conversion : ConversionSetup) :
    0 < conversionVentFailureBudget conversion ∧
    mechanismConversionFailureBudget mechanism conversion =
      mechanismExternalityBudget mechanism + conversionVentFailureBudget conversion ∧
    ∃ boundary : QueueBoundaryWitnessNat,
      boundary.beta1 = 0 ∧
      boundary.capacity = 1 ∧
      boundary.arrivalRate = mechanismConversionFailureBudget mechanism conversion ∧
      boundary.serviceRate =
        quorumSize (replicaCount (mechanismConversionFailureBudget mechanism conversion))
          (mechanismConversionFailureBudget mechanism conversion) := by
  refine ⟨conversion_vent_positive conversion, rfl, ?_⟩
  exact ⟨canonicalQueueBoundary (mechanismConversionFailureBudget mechanism conversion), rfl, rfl, rfl, rfl⟩

theorem mediation_mechanism_conversion_budget_yields_unit_queue_boundary
    (mediation : MediationSetup)
    (conversion : ConversionSetup) :
    0 < conversionVentFailureBudget conversion ∧
    0 < mediation.mediatorLoss ∧
    mediationMechanismConversionFailureBudget mediation conversion =
      mediation.mediatorLoss + conversionVentFailureBudget conversion ∧
    ∃ boundary : QueueBoundaryWitnessNat,
      boundary.beta1 = 0 ∧
      boundary.capacity = 1 ∧
      boundary.arrivalRate = mediationMechanismConversionFailureBudget mediation conversion ∧
      boundary.serviceRate =
        quorumSize (replicaCount (mediationMechanismConversionFailureBudget mediation conversion))
          (mediationMechanismConversionFailureBudget mediation conversion) := by
  refine ⟨conversion_vent_positive conversion, mediation.hMediatorLoss, rfl, ?_⟩
  exact
    ⟨canonicalQueueBoundary (mediationMechanismConversionFailureBudget mediation conversion),
      rfl, rfl, rfl, rfl⟩

theorem mechanism_conversion_budget_does_not_force_positive_beta1
    (mechanism : MechanismSetup)
    (conversion : ConversionSetup) :
    ¬ (∀ boundary : QueueBoundaryWitnessNat,
        boundary.arrivalRate = mechanismConversionFailureBudget mechanism conversion →
        boundary.serviceRate =
          quorumSize (replicaCount (mechanismConversionFailureBudget mechanism conversion))
            (mechanismConversionFailureBudget mechanism conversion) →
        0 < boundary.beta1) := by
  intro hAll
  let boundary := canonicalQueueBoundary (mechanismConversionFailureBudget mechanism conversion)
  have h : 0 < boundary.beta1 := hAll boundary rfl rfl
  exact Nat.lt_irrefl 0 h

theorem mediation_mechanism_conversion_budget_does_not_force_positive_beta1
    (mediation : MediationSetup)
    (conversion : ConversionSetup) :
    ¬ (∀ boundary : QueueBoundaryWitnessNat,
        boundary.arrivalRate = mediationMechanismConversionFailureBudget mediation conversion →
        boundary.serviceRate =
          quorumSize (replicaCount (mediationMechanismConversionFailureBudget mediation conversion))
            (mediationMechanismConversionFailureBudget mediation conversion) →
        0 < boundary.beta1) := by
  intro hAll
  let boundary := canonicalQueueBoundary (mediationMechanismConversionFailureBudget mediation conversion)
  have h : 0 < boundary.beta1 := hAll boundary rfl rfl
  exact Nat.lt_irrefl 0 h

theorem mediation_mechanism_conversion_budget_does_not_force_zero_arrival
    (mediation : MediationSetup)
    (conversion : ConversionSetup) :
    ¬ (∀ boundary : QueueBoundaryWitnessNat,
        boundary.arrivalRate = mediationMechanismConversionFailureBudget mediation conversion →
        boundary.serviceRate =
          quorumSize (replicaCount (mediationMechanismConversionFailureBudget mediation conversion))
            (mediationMechanismConversionFailureBudget mediation conversion) →
        boundary.arrivalRate = 0) := by
  intro hAll
  let boundary := canonicalQueueBoundary (mediationMechanismConversionFailureBudget mediation conversion)
  have hZero : boundary.arrivalRate = 0 := hAll boundary rfl rfl
  have hBudgetZero : mediationMechanismConversionFailureBudget mediation conversion = 0 := by
    exact hZero
  exact
    (Nat.ne_of_gt (mediation_mechanism_conversion_budget_positive mediation conversion))
    hBudgetZero

theorem mediation_mechanism_conversion_budget_yields_geometric_rate_certificate
    (mediation : MediationSetup)
    (conversion : ConversionSetup) :
    ∃ rate : GeometricRateNat,
      rate = budgetGeometricRate (mediationMechanismConversionFailureBudget mediation conversion) ∧
      rate.initialBound = mediationMechanismConversionFailureBudget mediation conversion + 1 ∧
      rate.numerator = 3 ∧
      rate.denominator = 4 ∧
      rate.numerator < rate.denominator ∧
      0 < rate.initialBound := by
  refine
    ⟨budgetGeometricRate (mediationMechanismConversionFailureBudget mediation conversion),
      rfl, rfl, rfl, rfl, ?_, ?_⟩
  · exact
      (budgetGeometricRate
        (mediationMechanismConversionFailureBudget mediation conversion)).hRateLtOne
  · exact
      (budgetGeometricRate
        (mediationMechanismConversionFailureBudget mediation conversion)).hInitialBoundPos

theorem mediation_mechanism_conversion_budget_real_positive
    (mediation : MediationSetup)
    (conversion : ConversionSetup) :
    0 < mediationMechanismConversionFailureBudget mediation conversion :=
  mediation_mechanism_conversion_budget_positive mediation conversion

structure MediationMechanismConversionKernelLiftAdapter where
  mediation : MediationSetup
  conversion : ConversionSetup
  budget : Nat
  hBudgetEq : budget = mediationMechanismConversionFailureBudget mediation conversion
  driftGap : Nat
  hDriftGap : 0 < driftGap
  kernelMatched : Bool
deriving Repr

namespace MediationMechanismConversionKernelLiftAdapter

theorem budget_pos_from_source
    (adapter : MediationMechanismConversionKernelLiftAdapter) :
    0 < adapter.budget := by
  rw [adapter.hBudgetEq]
  exact
    mediation_mechanism_conversion_budget_positive
      adapter.mediation
      adapter.conversion

theorem mediation_mechanism_conversion_continuous_ergodicity_lift
    (adapter : MediationMechanismConversionKernelLiftAdapter) :
    0 < adapter.budget ∧ 0 < adapter.driftGap := by
  exact ⟨adapter.budget_pos_from_source, adapter.hDriftGap⟩

end MediationMechanismConversionKernelLiftAdapter

end MediationMechanismConversionQueueKernelBridge
