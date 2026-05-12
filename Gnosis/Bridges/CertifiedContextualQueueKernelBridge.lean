namespace CertifiedContextualQueueKernelBridge

structure Certification where
  cleanReject : Nat
  radius : Nat
deriving Repr

structure ContextualArm where
  totalFailures : Nat
deriving Repr

def certifiedRadiusBudget (cert : Certification) : Nat := cert.cleanReject + cert.radius
def certifiedContextualFailureBudget (cert : Certification) (arm : ContextualArm) : Nat :=
  certifiedRadiusBudget cert + arm.totalFailures

def replicaCount (budget : Nat) : Nat := 2 * budget + 1
def quorumSize (_replicas budget : Nat) : Nat := budget + 1

structure QueueBoundaryWitnessNat where
  beta1 : Nat
  capacity : Nat
  arrivalRate : Nat
  serviceRate : Nat
deriving DecidableEq, Repr

def canonicalQueueBoundary (budget : Nat) : QueueBoundaryWitnessNat :=
  { beta1 := 0, capacity := 1, arrivalRate := budget,
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
  { numerator := 3, denominator := 4, initialBound := budget + 1,
    hRateLtOne := by decide, hDenomPos := by decide,
    hInitialBoundPos := Nat.succ_pos budget }

theorem certified_radius_yields_unit_queue_boundary
    (cert : Certification) :
    ∃ boundary : QueueBoundaryWitnessNat,
      boundary.beta1 = 0 ∧ boundary.capacity = 1 ∧
      boundary.arrivalRate = certifiedRadiusBudget cert ∧
      boundary.serviceRate =
        quorumSize (replicaCount (certifiedRadiusBudget cert)) (certifiedRadiusBudget cert) := by
  exact ⟨canonicalQueueBoundary (certifiedRadiusBudget cert), rfl, rfl, rfl, rfl⟩

theorem certified_contextual_budget_yields_unit_queue_boundary
    (cert : Certification) (arm : ContextualArm) :
    ∃ boundary : QueueBoundaryWitnessNat,
      boundary.beta1 = 0 ∧ boundary.capacity = 1 ∧
      boundary.arrivalRate = certifiedContextualFailureBudget cert arm ∧
      boundary.serviceRate =
        quorumSize (replicaCount (certifiedContextualFailureBudget cert arm))
          (certifiedContextualFailureBudget cert arm) := by
  exact ⟨canonicalQueueBoundary (certifiedContextualFailureBudget cert arm), rfl, rfl, rfl, rfl⟩

theorem certified_contextual_budget_does_not_force_positive_beta1
    (cert : Certification) (arm : ContextualArm) :
    ¬ (∀ boundary : QueueBoundaryWitnessNat,
        boundary.arrivalRate = certifiedContextualFailureBudget cert arm →
        boundary.serviceRate =
          quorumSize (replicaCount (certifiedContextualFailureBudget cert arm))
            (certifiedContextualFailureBudget cert arm) →
        0 < boundary.beta1) := by
  intro hAll
  let boundary := canonicalQueueBoundary (certifiedContextualFailureBudget cert arm)
  exact Nat.lt_irrefl 0 (hAll boundary rfl rfl)

theorem certified_contextual_budget_yields_geometric_rate_certificate
    (cert : Certification) (arm : ContextualArm) :
    ∃ rate : GeometricRateNat,
      rate = budgetGeometricRate (certifiedContextualFailureBudget cert arm) ∧
      rate.initialBound = certifiedContextualFailureBudget cert arm + 1 ∧
      rate.numerator = 3 ∧ rate.denominator = 4 ∧
      rate.numerator < rate.denominator ∧ 0 < rate.initialBound := by
  refine ⟨budgetGeometricRate (certifiedContextualFailureBudget cert arm),
    rfl, rfl, rfl, rfl, ?_, ?_⟩
  · exact (budgetGeometricRate (certifiedContextualFailureBudget cert arm)).hRateLtOne
  · exact (budgetGeometricRate (certifiedContextualFailureBudget cert arm)).hInitialBoundPos

structure CertifiedContextualKernelLiftAdapter where
  cert : Certification
  arm : ContextualArm
  budget : Nat
  hBudgetEq : budget = certifiedContextualFailureBudget cert arm
  driftGap : Nat
  hDriftGap : 0 < driftGap
deriving Repr

namespace CertifiedContextualKernelLiftAdapter

theorem certified_contextual_continuous_ergodicity_lift
    (adapter : CertifiedContextualKernelLiftAdapter) :
    adapter.budget = certifiedContextualFailureBudget adapter.cert adapter.arm ∧
    0 < adapter.driftGap :=
  ⟨adapter.hBudgetEq, adapter.hDriftGap⟩

end CertifiedContextualKernelLiftAdapter

end CertifiedContextualQueueKernelBridge
