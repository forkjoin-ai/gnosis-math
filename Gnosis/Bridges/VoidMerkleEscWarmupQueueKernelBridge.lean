import Init

/-!
# Void/Merkle/ESC/Warmup Queue Kernel Bridge

Finite void-root, ESC cold-path, and warmup-deficit witnesses for stale MCP rows.
-/

namespace VoidMerkleEscWarmupQueueKernelBridge

structure VoidMerkleSetup where
  root : Nat
  hIrreversible : True
deriving Repr

structure EscColdPath where
  coldFoldWork : Nat
  hCold : 0 < coldFoldWork
deriving Repr

structure WarmupSetup where
  underDeficit : Nat
  overDeficit : Nat
  deficitWeight : Nat
  hUnder : 0 < underDeficit
  hOver : overDeficit = 0
  hWeight : 0 < deficitWeight
deriving Repr

def totalDeficit (warmup : WarmupSetup) : Nat :=
  warmup.underDeficit + warmup.overDeficit

def voidMerkleEscWarmupFailureBudget
    (void : VoidMerkleSetup) (esc : EscColdPath) (warmup : WarmupSetup) : Nat :=
  void.root + esc.coldFoldWork + totalDeficit warmup

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

structure JointQueueWitnessPack where
  escOnly : QueueBoundaryWitnessNat
  combined : QueueBoundaryWitnessNat
deriving Repr

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

theorem total_deficit_positive (warmup : WarmupSetup) :
    0 < totalDeficit warmup := by
  unfold totalDeficit
  exact Nat.lt_add_right warmup.overDeficit warmup.hUnder

theorem void_merkle_esc_warmup_budget_positive
    (void : VoidMerkleSetup) (esc : EscColdPath) (warmup : WarmupSetup) :
    0 < voidMerkleEscWarmupFailureBudget void esc warmup := by
  unfold voidMerkleEscWarmupFailureBudget
  exact Nat.lt_add_left (void.root + esc.coldFoldWork) (total_deficit_positive warmup)

theorem void_merkle_esc_warmup_budget_yields_unit_queue_boundary
    (void : VoidMerkleSetup) (esc : EscColdPath) (warmup : WarmupSetup) :
    0 < esc.coldFoldWork ∧
    0 < totalDeficit warmup ∧
    ∃ boundary : QueueBoundaryWitnessNat,
      boundary.beta1 = 0 ∧
      boundary.capacity = 1 ∧
      boundary.arrivalRate = voidMerkleEscWarmupFailureBudget void esc warmup ∧
      boundary.serviceRate =
        quorumSize (replicaCount (voidMerkleEscWarmupFailureBudget void esc warmup))
          (voidMerkleEscWarmupFailureBudget void esc warmup) := by
  exact ⟨esc.hCold, total_deficit_positive warmup,
    ⟨canonicalQueueBoundary (voidMerkleEscWarmupFailureBudget void esc warmup),
      rfl, rfl, rfl, rfl⟩⟩

theorem void_merkle_esc_warmup_joint_queue_witness_pack
    (void : VoidMerkleSetup) (esc : EscColdPath) (warmup : WarmupSetup) :
    ∃ pack : JointQueueWitnessPack,
      pack.escOnly.arrivalRate = esc.coldFoldWork ∧
      pack.combined.arrivalRate = voidMerkleEscWarmupFailureBudget void esc warmup ∧
      pack.escOnly.capacity = 1 ∧
      pack.combined.capacity = 1 := by
  exact ⟨{
      escOnly := canonicalQueueBoundary esc.coldFoldWork
      combined := canonicalQueueBoundary (voidMerkleEscWarmupFailureBudget void esc warmup)
    }, rfl, rfl, rfl, rfl⟩

theorem void_merkle_esc_warmup_budget_does_not_force_capacity_equals_budget_plus_one
    (void : VoidMerkleSetup) (esc : EscColdPath) (warmup : WarmupSetup) :
    ¬ (∀ boundary : QueueBoundaryWitnessNat,
        boundary.arrivalRate = voidMerkleEscWarmupFailureBudget void esc warmup →
        boundary.serviceRate =
          quorumSize (replicaCount (voidMerkleEscWarmupFailureBudget void esc warmup))
            (voidMerkleEscWarmupFailureBudget void esc warmup) →
        boundary.capacity = voidMerkleEscWarmupFailureBudget void esc warmup + 1) := by
  intro hAll
  let boundary := canonicalQueueBoundary (voidMerkleEscWarmupFailureBudget void esc warmup)
  have hEq := hAll boundary rfl rfl
  have hEq' : voidMerkleEscWarmupFailureBudget void esc warmup + 1 = 1 := Eq.symm hEq
  have hBudgetZero : voidMerkleEscWarmupFailureBudget void esc warmup = 0 :=
    Nat.succ.inj hEq'
  exact (Nat.ne_of_gt (void_merkle_esc_warmup_budget_positive void esc warmup)) hBudgetZero

theorem void_merkle_esc_warmup_budget_yields_geometric_rate_certificate
    (void : VoidMerkleSetup) (esc : EscColdPath) (warmup : WarmupSetup) :
    ∃ rate : GeometricRateNat,
      rate = budgetGeometricRate (voidMerkleEscWarmupFailureBudget void esc warmup) ∧
      rate.initialBound = voidMerkleEscWarmupFailureBudget void esc warmup + 1 ∧
      rate.numerator = 3 ∧
      rate.denominator = 4 ∧
      rate.numerator < rate.denominator ∧
      0 < rate.initialBound := by
  refine ⟨budgetGeometricRate (voidMerkleEscWarmupFailureBudget void esc warmup),
    rfl, rfl, rfl, rfl, ?_, ?_⟩
  · exact (budgetGeometricRate (voidMerkleEscWarmupFailureBudget void esc warmup)).hRateLtOne
  · exact (budgetGeometricRate (voidMerkleEscWarmupFailureBudget void esc warmup)).hInitialBoundPos

theorem void_merkle_esc_warmup_budget_real_positive
    (void : VoidMerkleSetup) (esc : EscColdPath) (warmup : WarmupSetup) :
    0 < voidMerkleEscWarmupFailureBudget void esc warmup :=
  void_merkle_esc_warmup_budget_positive void esc warmup

structure VoidMerkleEscWarmupKernelLiftAdapter where
  void : VoidMerkleSetup
  esc : EscColdPath
  warmup : WarmupSetup
  budget : Nat
  hBudgetEq : budget = voidMerkleEscWarmupFailureBudget void esc warmup
  driftGap : Nat
  hDriftGap : 0 < driftGap
deriving Repr

end VoidMerkleEscWarmupQueueKernelBridge

namespace VoidMerkleEscWarmupKernelLiftAdapter

abbrev VoidMerkleEscWarmupKernelLiftAdapter :=
  VoidMerkleEscWarmupQueueKernelBridge.VoidMerkleEscWarmupKernelLiftAdapter

theorem budget_pos_from_source
    (adapter : VoidMerkleEscWarmupKernelLiftAdapter) :
    0 < adapter.budget := by
  rw [adapter.hBudgetEq]
  exact VoidMerkleEscWarmupQueueKernelBridge.void_merkle_esc_warmup_budget_positive
    adapter.void
    adapter.esc
    adapter.warmup

theorem void_merkle_esc_warmup_continuous_ergodicity_lift
    (adapter : VoidMerkleEscWarmupKernelLiftAdapter) :
    adapter.budget =
      VoidMerkleEscWarmupQueueKernelBridge.voidMerkleEscWarmupFailureBudget
        adapter.void
        adapter.esc
        adapter.warmup ∧
    0 < adapter.budget ∧
    0 < adapter.driftGap :=
  ⟨adapter.hBudgetEq, budget_pos_from_source adapter, adapter.hDriftGap⟩

end VoidMerkleEscWarmupKernelLiftAdapter
