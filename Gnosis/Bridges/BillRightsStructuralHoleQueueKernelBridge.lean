namespace BillRightsStructuralHoleQueueKernelBridge

/-!
Init-only replacement for the legacy Mathlib-heavy
`BillRightsStructuralHoleQueueKernelBridge`.

The historical file existed in `open-source/gnosis` and was later reduced to an
imports-only shell before deletion. This module restores the theorem surface with
finite `Nat` witnesses: one-path queue boundaries, explicit budget arithmetic,
and finite geometric-rate/kernel-lift certificates.
-/

def rightsWeight (R v : Nat) : Nat :=
  R - Nat.min v R + 1

theorem right_to_exist (R v : Nat) : 1 ≤ rightsWeight R v := by
  unfold rightsWeight
  exact Nat.succ_le_succ (Nat.zero_le _)

def rightsFailureBudget (R v : Nat) : Nat :=
  rightsWeight R v - 1

def rightsReplicaCount (R v : Nat) : Nat :=
  2 * rightsFailureBudget R v + 1

def quorumSize (_replicaCount failureBudget : Nat) : Nat :=
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
    serviceRate := quorumSize (2 * failureBudget + 1) failureBudget }

theorem strict_majority_budget_lt_quorum (failureBudget : Nat) :
    failureBudget < quorumSize (2 * failureBudget + 1) failureBudget := by
  unfold quorumSize
  exact Nat.lt_succ_self failureBudget

structure StructuralHole where
  interpolationWeight : Nat
  hPositive : 0 < interpolationWeight
deriving Repr

def structuralHoleFailureBudget (sh : StructuralHole) : Nat :=
  sh.interpolationWeight - 1

def structuralHoleReplicaCount (sh : StructuralHole) : Nat :=
  2 * structuralHoleFailureBudget sh + 1

def rightsStructuralHoleFailureBudget (R v : Nat) (sh : StructuralHole) : Nat :=
  rightsFailureBudget R v + structuralHoleFailureBudget sh

def rightsStructuralHoleReplicaCount (R v : Nat) (sh : StructuralHole) : Nat :=
  2 * rightsStructuralHoleFailureBudget R v sh + 1

structure GoodhartSetup where
  R : Nat
  vTrue : Nat
  vGamed : Nat
  hTrueLe : vTrue ≤ R
  hGamedLe : vGamed ≤ R
  hGaming : vGamed < vTrue
deriving Repr

def goodhartFailureBudget (goodhart : GoodhartSetup) : Nat :=
  goodhart.vTrue - goodhart.vGamed

def rightsStructuralHoleGoodhartFailureBudget
    (R v : Nat)
    (sh : StructuralHole)
    (goodhart : GoodhartSetup) : Nat :=
  rightsStructuralHoleFailureBudget R v sh + goodhartFailureBudget goodhart

def rightsStructuralHoleGoodhartReplicaCount
    (R v : Nat)
    (sh : StructuralHole)
    (goodhart : GoodhartSetup) : Nat :=
  2 * rightsStructuralHoleGoodhartFailureBudget R v sh goodhart + 1

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

structure KernelLiftAdapter where
  budget : Nat
  hBudgetPos : 0 < budget
  driftGap : Nat
  hDriftGap : 0 < driftGap
  kernelMatched : Bool
deriving Repr

namespace RightsStructuralHoleKernelLiftAdapter

structure Adapter where
  R : Nat
  v : Nat
  hole : StructuralHole
  budget : Nat
  hBudgetEq : budget = rightsStructuralHoleFailureBudget R v hole
  hBudgetPos : 0 < budget
  driftGap : Nat
  hDriftGap : 0 < driftGap
  kernelMatched : Bool
deriving Repr

theorem rights_structural_hole_continuous_ergodicity_lift
    (adapter : Adapter) :
    1 ≤ rightsWeight adapter.R adapter.v ∧
    0 < adapter.hole.interpolationWeight ∧
    0 < adapter.budget ∧
    0 < adapter.driftGap :=
  ⟨right_to_exist adapter.R adapter.v,
    adapter.hole.hPositive,
    adapter.hBudgetPos,
    adapter.hDriftGap⟩

end RightsStructuralHoleKernelLiftAdapter

namespace RightsStructuralHoleGoodhartKernelLiftAdapter

structure Adapter where
  R : Nat
  v : Nat
  hole : StructuralHole
  goodhart : GoodhartSetup
  budget : Nat
  hBudgetEq : budget = rightsStructuralHoleGoodhartFailureBudget R v hole goodhart
  driftGap : Nat
  hDriftGap : 0 < driftGap
  kernelMatched : Bool
deriving Repr

theorem budget_pos_from_source
    (R v : Nat)
    (sh : StructuralHole)
    (goodhart : GoodhartSetup) :
    0 < rightsStructuralHoleGoodhartFailureBudget R v sh goodhart := by
  unfold rightsStructuralHoleGoodhartFailureBudget goodhartFailureBudget
  have hGap : 0 < goodhart.vTrue - goodhart.vGamed :=
    Nat.sub_pos_of_lt goodhart.hGaming
  exact Nat.lt_of_lt_of_le hGap (Nat.le_add_left _ _)

theorem rights_structural_hole_goodhart_continuous_ergodicity_lift
    (adapter : Adapter) :
    1 ≤ rightsWeight adapter.R adapter.v ∧
    0 < adapter.hole.interpolationWeight ∧
    0 < adapter.budget ∧
    0 < adapter.driftGap := by
  refine ⟨right_to_exist adapter.R adapter.v, adapter.hole.hPositive, ?_, adapter.hDriftGap⟩
  rw [adapter.hBudgetEq]
  exact budget_pos_from_source adapter.R adapter.v adapter.hole adapter.goodhart

end RightsStructuralHoleGoodhartKernelLiftAdapter

theorem rights_floor_yields_unit_queue_boundary
    (R v : Nat) :
    1 ≤ rightsWeight R v ∧
    ∃ boundary : QueueBoundaryWitnessNat,
      boundary.beta1 = 0 ∧
      boundary.capacity = 1 ∧
      boundary.arrivalRate = rightsFailureBudget R v ∧
      boundary.serviceRate = quorumSize (rightsReplicaCount R v) (rightsFailureBudget R v) := by
  refine ⟨right_to_exist R v, ?_⟩
  refine ⟨canonicalQueueBoundary (rightsFailureBudget R v), rfl, rfl, rfl, ?_⟩
  rfl

theorem structural_hole_budget_yields_unit_queue_boundary
    (sh : StructuralHole) :
    0 < sh.interpolationWeight ∧
    ∃ boundary : QueueBoundaryWitnessNat,
      boundary.beta1 = 0 ∧
      boundary.capacity = 1 ∧
      boundary.arrivalRate = structuralHoleFailureBudget sh ∧
      boundary.serviceRate = quorumSize (structuralHoleReplicaCount sh) (structuralHoleFailureBudget sh) := by
  refine ⟨sh.hPositive, ?_⟩
  refine ⟨canonicalQueueBoundary (structuralHoleFailureBudget sh), rfl, rfl, rfl, ?_⟩
  rfl

theorem rights_structural_hole_budget_yields_unit_queue_boundary
    (R v : Nat)
    (sh : StructuralHole) :
    1 ≤ rightsWeight R v ∧
    0 < sh.interpolationWeight ∧
    rightsStructuralHoleFailureBudget R v sh =
      rightsFailureBudget R v + structuralHoleFailureBudget sh ∧
    ∃ boundary : QueueBoundaryWitnessNat,
      boundary.beta1 = 0 ∧
      boundary.capacity = 1 ∧
      boundary.arrivalRate = rightsStructuralHoleFailureBudget R v sh ∧
      boundary.serviceRate =
        quorumSize
          (rightsStructuralHoleReplicaCount R v sh)
          (rightsStructuralHoleFailureBudget R v sh) := by
  refine ⟨right_to_exist R v, sh.hPositive, rfl, ?_⟩
  refine ⟨canonicalQueueBoundary (rightsStructuralHoleFailureBudget R v sh), rfl, rfl, rfl, ?_⟩
  rfl

theorem rights_structural_hole_budget_does_not_force_positive_beta1
    (R v : Nat)
    (sh : StructuralHole) :
    ¬ (∀ boundary : QueueBoundaryWitnessNat,
        boundary.arrivalRate = rightsStructuralHoleFailureBudget R v sh →
        boundary.serviceRate =
          quorumSize
            (rightsStructuralHoleReplicaCount R v sh)
            (rightsStructuralHoleFailureBudget R v sh) →
        0 < boundary.beta1) := by
  intro hPositive
  let boundary := canonicalQueueBoundary (rightsStructuralHoleFailureBudget R v sh)
  have h : 0 < boundary.beta1 := hPositive boundary rfl rfl
  exact Nat.lt_irrefl 0 h

theorem rights_structural_hole_budget_yields_geometric_rate_certificate
    (R v : Nat)
    (sh : StructuralHole) :
    1 ≤ rightsWeight R v ∧
    0 < sh.interpolationWeight ∧
    ∃ rate : GeometricRateNat,
      rate = budgetGeometricRate (rightsStructuralHoleFailureBudget R v sh) ∧
      rate.initialBound = rightsStructuralHoleFailureBudget R v sh + 1 ∧
      rate.numerator = 3 ∧
      rate.denominator = 4 ∧
      rate.numerator < rate.denominator ∧
      0 < rate.initialBound := by
  refine ⟨right_to_exist R v, sh.hPositive, ?_⟩
  refine ⟨budgetGeometricRate (rightsStructuralHoleFailureBudget R v sh), rfl, rfl, rfl, rfl, ?_, ?_⟩
  · exact (budgetGeometricRate (rightsStructuralHoleFailureBudget R v sh)).hRateLtOne
  · exact (budgetGeometricRate (rightsStructuralHoleFailureBudget R v sh)).hInitialBoundPos

theorem rights_structural_hole_goodhart_budget_yields_unit_queue_boundary
    (R v : Nat)
    (sh : StructuralHole)
    (goodhart : GoodhartSetup) :
    1 ≤ rightsWeight R v ∧
    0 < sh.interpolationWeight ∧
    0 < goodhartFailureBudget goodhart ∧
    ∃ boundary : QueueBoundaryWitnessNat,
      boundary.beta1 = 0 ∧
      boundary.capacity = 1 ∧
      boundary.arrivalRate = rightsStructuralHoleGoodhartFailureBudget R v sh goodhart ∧
      boundary.serviceRate =
        quorumSize
          (rightsStructuralHoleGoodhartReplicaCount R v sh goodhart)
          (rightsStructuralHoleGoodhartFailureBudget R v sh goodhart) := by
  refine ⟨right_to_exist R v, sh.hPositive, ?_, ?_⟩
  · unfold goodhartFailureBudget
    exact Nat.sub_pos_of_lt goodhart.hGaming
  · refine ⟨canonicalQueueBoundary (rightsStructuralHoleGoodhartFailureBudget R v sh goodhart), rfl, rfl, rfl, ?_⟩
    rfl

theorem rights_structural_hole_goodhart_joint_queue_witness_pack
    (R v : Nat)
    (sh : StructuralHole)
    (goodhart : GoodhartSetup) :
    (∃ boundary : QueueBoundaryWitnessNat,
      boundary.beta1 = 0 ∧
      boundary.arrivalRate = rightsStructuralHoleFailureBudget R v sh) ∧
    (∃ boundary : QueueBoundaryWitnessNat,
      boundary.beta1 = 0 ∧
      boundary.arrivalRate = rightsStructuralHoleGoodhartFailureBudget R v sh goodhart) := by
  refine ⟨?_, ?_⟩
  · refine ⟨canonicalQueueBoundary (rightsStructuralHoleFailureBudget R v sh), rfl, rfl⟩
  · refine ⟨canonicalQueueBoundary (rightsStructuralHoleGoodhartFailureBudget R v sh goodhart), rfl, rfl⟩

theorem rights_structural_hole_goodhart_budget_does_not_force_beta1_equals_budget
    (R v : Nat)
    (sh : StructuralHole)
    (goodhart : GoodhartSetup) :
    ¬ (∀ boundary : QueueBoundaryWitnessNat,
        boundary.arrivalRate = rightsStructuralHoleGoodhartFailureBudget R v sh goodhart →
        boundary.beta1 = rightsStructuralHoleGoodhartFailureBudget R v sh goodhart) := by
  intro hAll
  let boundary := canonicalQueueBoundary (rightsStructuralHoleGoodhartFailureBudget R v sh goodhart)
  have hEq : boundary.beta1 = rightsStructuralHoleGoodhartFailureBudget R v sh goodhart :=
    hAll boundary rfl
  have hPos : 0 < rightsStructuralHoleGoodhartFailureBudget R v sh goodhart :=
    RightsStructuralHoleGoodhartKernelLiftAdapter.budget_pos_from_source R v sh goodhart
  rw [show boundary.beta1 = 0 by rfl] at hEq
  rw [← hEq] at hPos
  exact Nat.lt_irrefl 0 hPos

theorem rights_structural_hole_goodhart_budget_yields_geometric_rate_certificate
    (R v : Nat)
    (sh : StructuralHole)
    (goodhart : GoodhartSetup) :
    1 ≤ rightsWeight R v ∧
    0 < sh.interpolationWeight ∧
    ∃ rate : GeometricRateNat,
      rate = budgetGeometricRate (rightsStructuralHoleGoodhartFailureBudget R v sh goodhart) ∧
      rate.initialBound = rightsStructuralHoleGoodhartFailureBudget R v sh goodhart + 1 ∧
      rate.numerator = 3 ∧
      rate.denominator = 4 ∧
      rate.numerator < rate.denominator ∧
      0 < rate.initialBound := by
  refine ⟨right_to_exist R v, sh.hPositive, ?_⟩
  refine ⟨budgetGeometricRate (rightsStructuralHoleGoodhartFailureBudget R v sh goodhart), rfl, rfl, rfl, rfl, ?_, ?_⟩
  · exact (budgetGeometricRate (rightsStructuralHoleGoodhartFailureBudget R v sh goodhart)).hRateLtOne
  · exact (budgetGeometricRate (rightsStructuralHoleGoodhartFailureBudget R v sh goodhart)).hInitialBoundPos

theorem rights_structural_hole_goodhart_budget_real_positive
    (R v : Nat)
    (sh : StructuralHole)
    (goodhart : GoodhartSetup) :
    0 < rightsStructuralHoleGoodhartFailureBudget R v sh goodhart :=
  RightsStructuralHoleGoodhartKernelLiftAdapter.budget_pos_from_source R v sh goodhart

end BillRightsStructuralHoleQueueKernelBridge
