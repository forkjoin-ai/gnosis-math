import Init
import Gnosis.GeometricErgodicity

/-!
# Form Topology Queue Kernel Bridge

Finite form-spec witnesses for stale form-topology MCP rows. The original
`FormTopology.lean` source is no longer present, so this bridge exposes the
needed form assumptions directly: well-formedness and a nonempty field surface.
-/

namespace FormTopologyQueueKernelBridge

structure FormSpec where
  fields : List Nat
  mappings : List Nat
deriving Repr

structure FormState where
  assignments : List Nat
deriving Repr

structure WellFormed (spec : FormSpec) (state : FormState) : Prop where
  hAssignable : spec.fields.length ≤ state.assignments.length + spec.fields.length

def formFailureBudget (spec : FormSpec) : Nat :=
  spec.fields.length + spec.mappings.length

def replicaCount (budget : Nat) : Nat := 2 * budget + 1

def quorumSize (_replicas budget : Nat) : Nat := budget + 1

def topologicalDeficit (paths streams : Nat) : Nat := paths - streams

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

theorem form_field_count_positive
    (spec : FormSpec)
    (hNonempty : ∃ field, field ∈ spec.fields) :
    0 < spec.fields.length := by
  rcases hNonempty with ⟨field, hField⟩
  exact List.length_pos_of_mem hField

theorem form_budget_positive
    (spec : FormSpec)
    (hNonempty : ∃ field, field ∈ spec.fields) :
    0 < formFailureBudget spec := by
  unfold formFailureBudget
  exact Nat.lt_add_right
    spec.mappings.length
    (form_field_count_positive spec hNonempty)

theorem form_well_formed_nonempty_yields_unit_queue_boundary
    (spec : FormSpec)
    (state : FormState)
    (_hWellFormed : WellFormed spec state)
    (hNonempty : ∃ field, field ∈ spec.fields) :
    0 < formFailureBudget spec ∧
    ∃ boundary : QueueBoundaryWitnessNat,
      boundary.beta1 = 0 ∧
      boundary.capacity = 1 ∧
      boundary.arrivalRate = formFailureBudget spec ∧
      boundary.serviceRate =
        quorumSize (replicaCount (formFailureBudget spec))
          (formFailureBudget spec) := by
  exact ⟨form_budget_positive spec hNonempty,
    ⟨canonicalQueueBoundary (formFailureBudget spec),
      rfl, rfl, rfl, rfl⟩⟩

theorem form_budget_yields_positive_topological_deficit
    (spec : FormSpec)
    (state : FormState)
    (_hWellFormed : WellFormed spec state)
    (hNonempty : ∃ field, field ∈ spec.fields) :
    0 < topologicalDeficit (formFailureBudget spec + 1) 1 := by
  unfold topologicalDeficit
  simpa using form_budget_positive spec hNonempty

theorem form_budget_does_not_force_capacity_at_least_two
    (spec : FormSpec)
    (state : FormState)
    (_hWellFormed : WellFormed spec state)
    (_hNonempty : ∃ field, field ∈ spec.fields) :
    ¬ (∀ boundary : QueueBoundaryWitnessNat,
        boundary.arrivalRate = formFailureBudget spec →
        boundary.serviceRate =
          quorumSize (replicaCount (formFailureBudget spec))
            (formFailureBudget spec) →
        2 ≤ boundary.capacity) := by
  intro hAll
  let boundary := canonicalQueueBoundary (formFailureBudget spec)
  have hCapacity : 2 ≤ 1 := hAll boundary rfl rfl
  exact (Nat.not_succ_le_self 1) hCapacity

theorem form_budget_yields_geometric_rate_certificate
    (spec : FormSpec)
    (state : FormState)
    (_hWellFormed : WellFormed spec state)
    (_hNonempty : ∃ field, field ∈ spec.fields) :
    ∃ rate : GeometricRateNat,
      rate = budgetGeometricRate (formFailureBudget spec) ∧
      rate.initialBound = formFailureBudget spec + 1 ∧
      rate.numerator = 3 ∧
      rate.denominator = 4 ∧
      rate.numerator < rate.denominator ∧
      0 < rate.initialBound := by
  refine ⟨budgetGeometricRate (formFailureBudget spec),
    rfl, rfl, rfl, rfl, ?_, ?_⟩
  · exact (budgetGeometricRate (formFailureBudget spec)).hRateLtOne
  · exact (budgetGeometricRate (formFailureBudget spec)).hInitialBoundPos

theorem form_budget_chapel_rate_initial_bound
    (spec : FormSpec) :
    (Gnosis.mkGeometricErgodicityRate
      3 4
      1 1
      1 1
      (formFailureBudget spec + 1)
      (by decide)
      (by decide)
      (by decide)
      (by decide)
      (by decide)
      (by decide)
      (by decide)
      (Nat.succ_pos (formFailureBudget spec))).initialBound =
      formFailureBudget spec + 1 := by
  rfl

end FormTopologyQueueKernelBridge
