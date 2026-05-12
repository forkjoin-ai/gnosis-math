import Init
import Gnosis.QuorumLinearizability

/-!
# Quorum Linearizability Queue Kernel Bridge

Append-then-read quorum linearizability routed through a finite write-count
queue interpretation.
-/

namespace QuorumLinearizabilityQueueKernelBridge

def writeCountAfterAppend (history : List Gnosis.LinearizedWrite) : Nat :=
  history.length + 1

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

theorem appended_linearized_read_refines_latest_prefix
    (history : List Gnosis.LinearizedWrite)
    (write : Gnosis.LinearizedWrite) :
    Gnosis.readRefinesPrefix
      (history ++ [write])
      { ballot := write.ballot
        writer := write.writer
        writeCount := writeCountAfterAppend history } := by
  exact Gnosis.read_after_appended_write_refines_new_latest history write

theorem linearized_read_interpretation_strict_majority
    (history : List Gnosis.LinearizedWrite) :
    quorumSize
        (replicaCount (writeCountAfterAppend history))
        (writeCountAfterAppend history) =
      writeCountAfterAppend history + 1 := by
  rfl

theorem appended_linearized_read_yields_unit_queue_boundary
    (history : List Gnosis.LinearizedWrite)
    (write : Gnosis.LinearizedWrite) :
    Gnosis.readRefinesPrefix
      (history ++ [write])
      { ballot := write.ballot
        writer := write.writer
        writeCount := writeCountAfterAppend history } ∧
    ∃ boundary : QueueBoundaryWitnessNat,
      boundary.beta1 = 0 ∧
      boundary.capacity = 1 ∧
      boundary.arrivalRate = writeCountAfterAppend history ∧
      boundary.serviceRate =
        quorumSize
          (replicaCount (writeCountAfterAppend history))
          (writeCountAfterAppend history) := by
  exact ⟨appended_linearized_read_refines_latest_prefix history write,
    ⟨canonicalQueueBoundary (writeCountAfterAppend history), rfl, rfl, rfl, rfl⟩⟩

theorem write_count_after_append_positive
    (history : List Gnosis.LinearizedWrite) :
    0 < writeCountAfterAppend history := by
  exact Nat.succ_pos history.length

theorem appended_linearized_read_does_not_force_beta1_equals_write_count
    (history : List Gnosis.LinearizedWrite) :
    ¬ (∀ boundary : QueueBoundaryWitnessNat,
        boundary.arrivalRate = writeCountAfterAppend history →
        boundary.serviceRate =
          quorumSize
            (replicaCount (writeCountAfterAppend history))
            (writeCountAfterAppend history) →
        boundary.beta1 = writeCountAfterAppend history) := by
  intro hAll
  let boundary := canonicalQueueBoundary (writeCountAfterAppend history)
  have hEq : boundary.beta1 = writeCountAfterAppend history :=
    hAll boundary rfl rfl
  have hPositive : 0 < writeCountAfterAppend history :=
    write_count_after_append_positive history
  rw [show boundary.beta1 = 0 by rfl] at hEq
  rw [← hEq] at hPositive
  exact Nat.lt_irrefl 0 hPositive

theorem appended_linearized_read_yields_geometric_rate_certificate
    (history : List Gnosis.LinearizedWrite) :
    ∃ rate : GeometricRateNat,
      rate = budgetGeometricRate (writeCountAfterAppend history) ∧
      rate.initialBound = writeCountAfterAppend history + 1 ∧
      rate.numerator = 3 ∧
      rate.denominator = 4 ∧
      rate.numerator < rate.denominator ∧
      0 < rate.initialBound := by
  refine ⟨budgetGeometricRate (writeCountAfterAppend history),
    rfl, rfl, rfl, rfl, ?_, ?_⟩
  · exact (budgetGeometricRate (writeCountAfterAppend history)).hRateLtOne
  · exact (budgetGeometricRate (writeCountAfterAppend history)).hInitialBoundPos

structure LinearizabilityKernelLiftBundle where
  history : List Gnosis.LinearizedWrite
  write : Gnosis.LinearizedWrite
  budget : Nat
  hBudgetEq : budget = writeCountAfterAppend history
  driftGap : Nat
  hDriftGap : 0 < driftGap
deriving Repr

end QuorumLinearizabilityQueueKernelBridge

namespace LinearizabilityKernelLiftAdapter

abbrev LinearizabilityKernelLiftBundle :=
  QuorumLinearizabilityQueueKernelBridge.LinearizabilityKernelLiftBundle

theorem linearized_read_continuous_ergodicity_lift
    (adapter : LinearizabilityKernelLiftBundle) :
    Gnosis.readRefinesPrefix
      (adapter.history ++ [adapter.write])
      { ballot := adapter.write.ballot
        writer := adapter.write.writer
        writeCount :=
          QuorumLinearizabilityQueueKernelBridge.writeCountAfterAppend adapter.history } ∧
    adapter.budget =
      QuorumLinearizabilityQueueKernelBridge.writeCountAfterAppend adapter.history ∧
    0 < adapter.driftGap :=
  ⟨QuorumLinearizabilityQueueKernelBridge.appended_linearized_read_refines_latest_prefix
      adapter.history
      adapter.write,
    adapter.hBudgetEq,
    adapter.hDriftGap⟩

end LinearizabilityKernelLiftAdapter
