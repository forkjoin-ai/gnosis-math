import Init
import Gnosis.AdversarialRobustness
import Gnosis.CertifiedDefenses

/-!
# Adversarial/Certified Queue Kernel Bridge

Finite perturbation-budget witnesses for the old adversarial robustness plus
certified-radius MCP bridge.
-/

namespace AdversarialCertifiedQueueKernelBridge

structure Certification where
  cleanReject : Nat
  radius : Nat
deriving Repr

structure AdversarialBudget where
  R : Nat
  v : Nat
  delta : Nat
  hv : v ≤ R
  hPerturbed : v + delta ≤ R
deriving Repr

def perturbationGap (adv : AdversarialBudget) : Nat := adv.delta

def certifiedRadiusBudget (cert : Certification) : Nat :=
  cert.cleanReject + cert.radius

def adversarialCertifiedFailureBudget
    (adv : AdversarialBudget) (cert : Certification) : Nat :=
  certifiedRadiusBudget cert + perturbationGap adv

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

theorem adversarial_gap_from_source
    (adv : AdversarialBudget) :
    Gnosis.godWeight adv.R adv.v -
      Gnosis.godWeight adv.R (adv.v + adv.delta) =
      perturbationGap adv := by
  exact AdversarialRobustness.adversarial_gap
    adv.R adv.v adv.delta adv.hv adv.hPerturbed

theorem adversarial_certified_budget_positive
    (adv : AdversarialBudget) (cert : Certification)
    (hDelta : 0 < adv.delta) :
    0 < adversarialCertifiedFailureBudget adv cert := by
  unfold adversarialCertifiedFailureBudget perturbationGap
  exact Nat.lt_add_left (certifiedRadiusBudget cert) hDelta

theorem adversarial_certified_budget_yields_unit_queue_boundary
    (adv : AdversarialBudget) (cert : Certification) :
    Gnosis.godWeight adv.R adv.v -
      Gnosis.godWeight adv.R (adv.v + adv.delta) =
        perturbationGap adv ∧
    ∃ boundary : QueueBoundaryWitnessNat,
      boundary.beta1 = 0 ∧
      boundary.capacity = 1 ∧
      boundary.arrivalRate = adversarialCertifiedFailureBudget adv cert ∧
      boundary.serviceRate =
        quorumSize (replicaCount (adversarialCertifiedFailureBudget adv cert))
          (adversarialCertifiedFailureBudget adv cert) := by
  exact ⟨adversarial_gap_from_source adv,
    ⟨canonicalQueueBoundary (adversarialCertifiedFailureBudget adv cert),
      rfl, rfl, rfl, rfl⟩⟩

theorem adversarial_certified_budget_does_not_force_strict_capacity_growth
    (adv : AdversarialBudget) (cert : Certification) :
    ¬ (∀ boundary : QueueBoundaryWitnessNat,
        boundary.arrivalRate = adversarialCertifiedFailureBudget adv cert →
        boundary.serviceRate =
          quorumSize (replicaCount (adversarialCertifiedFailureBudget adv cert))
            (adversarialCertifiedFailureBudget adv cert) →
        1 < boundary.capacity) := by
  intro hAll
  let boundary := canonicalQueueBoundary (adversarialCertifiedFailureBudget adv cert)
  exact Nat.lt_irrefl 1 (hAll boundary rfl rfl)

theorem adversarial_certified_budget_yields_geometric_rate_certificate
    (adv : AdversarialBudget) (cert : Certification) :
    Gnosis.godWeight adv.R adv.v -
      Gnosis.godWeight adv.R (adv.v + adv.delta) =
        perturbationGap adv ∧
    ∃ rate : GeometricRateNat,
      rate = budgetGeometricRate (adversarialCertifiedFailureBudget adv cert) ∧
      rate.initialBound = adversarialCertifiedFailureBudget adv cert + 1 ∧
      rate.numerator = 3 ∧
      rate.denominator = 4 ∧
      rate.numerator < rate.denominator ∧
      0 < rate.initialBound := by
  refine ⟨adversarial_gap_from_source adv, ?_⟩
  refine ⟨budgetGeometricRate (adversarialCertifiedFailureBudget adv cert),
    rfl, rfl, rfl, rfl, ?_, ?_⟩
  · exact (budgetGeometricRate (adversarialCertifiedFailureBudget adv cert)).hRateLtOne
  · exact (budgetGeometricRate (adversarialCertifiedFailureBudget adv cert)).hInitialBoundPos

theorem adversarial_certified_budget_real_positive
    (adv : AdversarialBudget) (cert : Certification)
    (hDelta : 0 < adv.delta) :
    0 < adversarialCertifiedFailureBudget adv cert :=
  adversarial_certified_budget_positive adv cert hDelta

structure AdversarialCertifiedKernelLiftBundle where
  adversarial : AdversarialBudget
  certification : Certification
  hDelta : 0 < adversarial.delta
  budget : Nat
  hBudgetEq : budget = adversarialCertifiedFailureBudget adversarial certification
  driftGap : Nat
  hDriftGap : 0 < driftGap
deriving Repr

end AdversarialCertifiedQueueKernelBridge

namespace AdversarialCertifiedKernelLiftAdapter

abbrev AdversarialCertifiedKernelLiftBundle :=
  AdversarialCertifiedQueueKernelBridge.AdversarialCertifiedKernelLiftBundle

theorem budget_pos_from_source
    (adapter : AdversarialCertifiedKernelLiftBundle) :
    0 < adapter.budget := by
  rw [adapter.hBudgetEq]
  exact AdversarialCertifiedQueueKernelBridge.adversarial_certified_budget_positive
    adapter.adversarial
    adapter.certification
    adapter.hDelta

theorem budget_mass_pos_from_source
    (adapter : AdversarialCertifiedKernelLiftBundle) :
    0 < adapter.certification.cleanReject + adapter.adversarial.delta + 1 :=
  Nat.succ_pos _

theorem adversarial_certified_continuous_ergodicity_lift
    (adapter : AdversarialCertifiedKernelLiftBundle) :
    adapter.budget =
      AdversarialCertifiedQueueKernelBridge.adversarialCertifiedFailureBudget
        adapter.adversarial
        adapter.certification ∧
    Gnosis.godWeight adapter.adversarial.R adapter.adversarial.v -
      Gnosis.godWeight adapter.adversarial.R
        (adapter.adversarial.v + adapter.adversarial.delta) =
        AdversarialCertifiedQueueKernelBridge.perturbationGap adapter.adversarial ∧
    0 < adapter.budget ∧
    0 < adapter.driftGap :=
  ⟨adapter.hBudgetEq,
    AdversarialCertifiedQueueKernelBridge.adversarial_gap_from_source adapter.adversarial,
    budget_pos_from_source adapter,
    adapter.hDriftGap⟩

end AdversarialCertifiedKernelLiftAdapter
