import Init
import Gnosis.BerksonsParadox
import Gnosis.Bridges.AdversarialCertifiedQueueKernelBridge
import Gnosis.Bridges.BerksonQueueKernelBridge

/-!
# Adversarial/Certified/Berkson Queue Kernel Bridge

Finite perturbation, certified-radius, and selected-collider witnesses for the
old tri-domain MCP bridge.
-/

namespace AdversarialCertifiedBerksonQueueKernelBridge

abbrev Certification := AdversarialCertifiedQueueKernelBridge.Certification
abbrev AdversarialBudget := AdversarialCertifiedQueueKernelBridge.AdversarialBudget

def perturbationGap (adv : AdversarialBudget) : Nat :=
  AdversarialCertifiedQueueKernelBridge.perturbationGap adv

def certifiedRadiusBudget (cert : Certification) : Nat :=
  AdversarialCertifiedQueueKernelBridge.certifiedRadiusBudget cert

def colliderThreshold (cs : BerksonsParadox.ColliderSetup) : Nat :=
  BerksonQueueKernelBridge.colliderThreshold cs

def adversarialCertifiedBerksonFailureBudget
    (adv : AdversarialBudget) (cert : Certification) (cs : BerksonsParadox.ColliderSetup) :
    Nat :=
  perturbationGap adv + certifiedRadiusBudget cert + colliderThreshold cs

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
  exact AdversarialCertifiedQueueKernelBridge.adversarial_gap_from_source adv

theorem selected_collider_threshold_bounded_by_total_rejections
    (cs : BerksonsParadox.ColliderSetup)
    (hSelected : cs.selected) :
    colliderThreshold cs ≤ BerksonQueueKernelBridge.totalRejections cs := by
  exact BerksonQueueKernelBridge.berkson_selected_implies_threshold_bounded_by_total_rejections
    cs
    hSelected

theorem adversarial_certified_berkson_budget_yields_unit_queue_boundary
    (adv : AdversarialBudget) (cert : Certification) (cs : BerksonsParadox.ColliderSetup)
    (hSelected : cs.selected) :
    Gnosis.godWeight adv.R adv.v -
      Gnosis.godWeight adv.R (adv.v + adv.delta) =
        perturbationGap adv ∧
    colliderThreshold cs ≤ BerksonQueueKernelBridge.totalRejections cs ∧
    ∃ boundary : QueueBoundaryWitnessNat,
      boundary.beta1 = 0 ∧
      boundary.capacity = 1 ∧
      boundary.arrivalRate = adversarialCertifiedBerksonFailureBudget adv cert cs ∧
      boundary.serviceRate =
        quorumSize (replicaCount (adversarialCertifiedBerksonFailureBudget adv cert cs))
          (adversarialCertifiedBerksonFailureBudget adv cert cs) := by
  exact ⟨adversarial_gap_from_source adv,
    selected_collider_threshold_bounded_by_total_rejections cs hSelected,
    ⟨canonicalQueueBoundary (adversarialCertifiedBerksonFailureBudget adv cert cs),
      rfl, rfl, rfl, rfl⟩⟩

theorem adversarial_certified_berkson_budget_does_not_force_strict_capacity_growth
    (adv : AdversarialBudget) (cert : Certification) (cs : BerksonsParadox.ColliderSetup) :
    ¬ (∀ boundary : QueueBoundaryWitnessNat,
        boundary.arrivalRate = adversarialCertifiedBerksonFailureBudget adv cert cs →
        boundary.serviceRate =
          quorumSize (replicaCount (adversarialCertifiedBerksonFailureBudget adv cert cs))
            (adversarialCertifiedBerksonFailureBudget adv cert cs) →
        1 < boundary.capacity) := by
  intro hAll
  let boundary := canonicalQueueBoundary (adversarialCertifiedBerksonFailureBudget adv cert cs)
  exact Nat.lt_irrefl 1 (hAll boundary rfl rfl)

theorem adversarial_certified_berkson_budget_yields_geometric_rate_certificate
    (adv : AdversarialBudget) (cert : Certification) (cs : BerksonsParadox.ColliderSetup)
    (hSelected : cs.selected) :
    Gnosis.godWeight adv.R adv.v -
      Gnosis.godWeight adv.R (adv.v + adv.delta) =
        perturbationGap adv ∧
    colliderThreshold cs ≤ BerksonQueueKernelBridge.totalRejections cs ∧
    ∃ rate : GeometricRateNat,
      rate = budgetGeometricRate (adversarialCertifiedBerksonFailureBudget adv cert cs) ∧
      rate.initialBound = adversarialCertifiedBerksonFailureBudget adv cert cs + 1 ∧
      rate.numerator = 3 ∧
      rate.denominator = 4 ∧
      rate.numerator < rate.denominator ∧
      0 < rate.initialBound := by
  refine ⟨adversarial_gap_from_source adv,
    selected_collider_threshold_bounded_by_total_rejections cs hSelected, ?_⟩
  refine ⟨budgetGeometricRate (adversarialCertifiedBerksonFailureBudget adv cert cs),
    rfl, rfl, rfl, rfl, ?_, ?_⟩
  · exact (budgetGeometricRate (adversarialCertifiedBerksonFailureBudget adv cert cs)).hRateLtOne
  · exact (budgetGeometricRate (adversarialCertifiedBerksonFailureBudget adv cert cs)).hInitialBoundPos

theorem adversarial_certified_berkson_budget_positive
    (adv : AdversarialBudget) (cert : Certification) (cs : BerksonsParadox.ColliderSetup)
    (hThreshold : 0 < colliderThreshold cs) :
    0 < adversarialCertifiedBerksonFailureBudget adv cert cs := by
  unfold adversarialCertifiedBerksonFailureBudget
  exact Nat.lt_add_left (perturbationGap adv + certifiedRadiusBudget cert) hThreshold

structure AdversarialCertifiedBerksonKernelLiftBundle where
  adversarial : AdversarialBudget
  certification : Certification
  collider : BerksonsParadox.ColliderSetup
  hSelected : collider.selected
  hThreshold : 0 < colliderThreshold collider
  budget : Nat
  hBudgetEq : budget =
    adversarialCertifiedBerksonFailureBudget adversarial certification collider
  driftGap : Nat
  hDriftGap : 0 < driftGap

end AdversarialCertifiedBerksonQueueKernelBridge

namespace AdversarialCertifiedBerksonKernelLiftAdapter

abbrev AdversarialCertifiedBerksonKernelLiftBundle :=
  AdversarialCertifiedBerksonQueueKernelBridge.AdversarialCertifiedBerksonKernelLiftBundle

theorem budget_pos_from_source
    (adapter : AdversarialCertifiedBerksonKernelLiftBundle) :
    0 < adapter.budget := by
  rw [adapter.hBudgetEq]
  exact AdversarialCertifiedBerksonQueueKernelBridge.adversarial_certified_berkson_budget_positive
    adapter.adversarial
    adapter.certification
    adapter.collider
    adapter.hThreshold

theorem adversarial_certified_berkson_continuous_ergodicity_lift
    (adapter : AdversarialCertifiedBerksonKernelLiftBundle) :
    adapter.budget =
      AdversarialCertifiedBerksonQueueKernelBridge.adversarialCertifiedBerksonFailureBudget
        adapter.adversarial
        adapter.certification
        adapter.collider ∧
    Gnosis.godWeight adapter.adversarial.R adapter.adversarial.v -
      Gnosis.godWeight adapter.adversarial.R
        (adapter.adversarial.v + adapter.adversarial.delta) =
        AdversarialCertifiedBerksonQueueKernelBridge.perturbationGap adapter.adversarial ∧
    AdversarialCertifiedBerksonQueueKernelBridge.colliderThreshold adapter.collider ≤
      BerksonQueueKernelBridge.totalRejections adapter.collider ∧
    0 < adapter.budget ∧
    0 < adapter.driftGap :=
  ⟨adapter.hBudgetEq,
    AdversarialCertifiedBerksonQueueKernelBridge.adversarial_gap_from_source adapter.adversarial,
    AdversarialCertifiedBerksonQueueKernelBridge.selected_collider_threshold_bounded_by_total_rejections
      adapter.collider
      adapter.hSelected,
    budget_pos_from_source adapter,
    adapter.hDriftGap⟩

end AdversarialCertifiedBerksonKernelLiftAdapter
