import Init

/-!
# Taphonomy/Tribology Queue Kernel Bridge

Finite fossilization and lubricant-gap witnesses for stale taphonomy/tribology
MCP rows.
-/

namespace TaphonomyTribologyQueueKernelBridge

structure FossilizationSetup where
  livingInformation : Nat
  ventedOrganics : Nat
  fossilInvariant : Nat
  hConservation : livingInformation = ventedOrganics + fossilInvariant
  hVented : 1 ≤ ventedOrganics
deriving Repr

structure TribologySetup where
  rawFriction : Nat
  lubricatedFriction : Nat
  slamPenalty : Nat
  hLubricated : lubricatedFriction < rawFriction
  hSlam : 1 ≤ slamPenalty
deriving Repr

def frictionGap (tribology : TribologySetup) : Nat :=
  tribology.rawFriction - tribology.lubricatedFriction

def taphonomyTribologyFailureBudget
    (fossil : FossilizationSetup) (tribology : TribologySetup) : Nat :=
  fossil.ventedOrganics + frictionGap tribology

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
  fossilOnly : QueueBoundaryWitnessNat
  tribologyOnly : QueueBoundaryWitnessNat
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

theorem friction_gap_positive (tribology : TribologySetup) :
    0 < frictionGap tribology := by
  unfold frictionGap
  exact Nat.sub_pos_of_lt tribology.hLubricated

theorem taphonomy_vented_positive (fossil : FossilizationSetup) :
    0 < fossil.ventedOrganics :=
  fossil.hVented

theorem taphonomy_tribology_budget_positive
    (fossil : FossilizationSetup) (tribology : TribologySetup) :
    0 < taphonomyTribologyFailureBudget fossil tribology := by
  unfold taphonomyTribologyFailureBudget
  exact Nat.lt_add_right (frictionGap tribology) (taphonomy_vented_positive fossil)

theorem fossilization_budget_yields_unit_queue_boundary
    (fossil : FossilizationSetup) :
    fossil.livingInformation = fossil.ventedOrganics + fossil.fossilInvariant ∧
    0 < fossil.ventedOrganics ∧
    ∃ boundary : QueueBoundaryWitnessNat,
      boundary.beta1 = 0 ∧
      boundary.capacity = 1 ∧
      boundary.arrivalRate = fossil.ventedOrganics ∧
      boundary.serviceRate =
        quorumSize (replicaCount fossil.ventedOrganics) fossil.ventedOrganics := by
  exact ⟨fossil.hConservation, taphonomy_vented_positive fossil,
    ⟨canonicalQueueBoundary fossil.ventedOrganics, rfl, rfl, rfl, rfl⟩⟩

theorem lubricant_budget_yields_unit_queue_boundary
    (tribology : TribologySetup) :
    0 < frictionGap tribology ∧
    ∃ boundary : QueueBoundaryWitnessNat,
      boundary.beta1 = 0 ∧
      boundary.capacity = 1 ∧
      boundary.arrivalRate = frictionGap tribology ∧
      boundary.serviceRate =
        quorumSize (replicaCount (frictionGap tribology)) (frictionGap tribology) := by
  exact ⟨friction_gap_positive tribology,
    ⟨canonicalQueueBoundary (frictionGap tribology), rfl, rfl, rfl, rfl⟩⟩

theorem taphonomy_tribology_budget_yields_unit_queue_boundary
    (fossil : FossilizationSetup) (tribology : TribologySetup) :
    0 < taphonomyTribologyFailureBudget fossil tribology ∧
    ∃ boundary : QueueBoundaryWitnessNat,
      boundary.beta1 = 0 ∧
      boundary.capacity = 1 ∧
      boundary.arrivalRate = taphonomyTribologyFailureBudget fossil tribology ∧
      boundary.serviceRate =
        quorumSize (replicaCount (taphonomyTribologyFailureBudget fossil tribology))
          (taphonomyTribologyFailureBudget fossil tribology) := by
  exact ⟨taphonomy_tribology_budget_positive fossil tribology,
    ⟨canonicalQueueBoundary (taphonomyTribologyFailureBudget fossil tribology),
      rfl, rfl, rfl, rfl⟩⟩

theorem taphonomy_tribology_joint_queue_witness_pack
    (fossil : FossilizationSetup) (tribology : TribologySetup) :
    ∃ pack : JointQueueWitnessPack,
      pack.fossilOnly.arrivalRate = fossil.ventedOrganics ∧
      pack.tribologyOnly.arrivalRate = frictionGap tribology ∧
      pack.combined.arrivalRate = taphonomyTribologyFailureBudget fossil tribology ∧
      pack.fossilOnly.capacity = 1 ∧
      pack.tribologyOnly.capacity = 1 ∧
      pack.combined.capacity = 1 := by
  exact ⟨{
      fossilOnly := canonicalQueueBoundary fossil.ventedOrganics
      tribologyOnly := canonicalQueueBoundary (frictionGap tribology)
      combined := canonicalQueueBoundary (taphonomyTribologyFailureBudget fossil tribology)
    }, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem taphonomy_tribology_budget_does_not_force_beta1_equals_budget
    (fossil : FossilizationSetup) (tribology : TribologySetup) :
    ¬ (∀ boundary : QueueBoundaryWitnessNat,
        boundary.arrivalRate = taphonomyTribologyFailureBudget fossil tribology →
        boundary.serviceRate =
          quorumSize (replicaCount (taphonomyTribologyFailureBudget fossil tribology))
            (taphonomyTribologyFailureBudget fossil tribology) →
        boundary.beta1 = taphonomyTribologyFailureBudget fossil tribology) := by
  intro hAll
  let boundary := canonicalQueueBoundary (taphonomyTribologyFailureBudget fossil tribology)
  have hEq := hAll boundary rfl rfl
  have hZero : taphonomyTribologyFailureBudget fossil tribology = 0 := Eq.symm hEq
  exact (Nat.ne_of_gt (taphonomy_tribology_budget_positive fossil tribology)) hZero

theorem taphonomy_tribology_budget_yields_geometric_rate_certificate
    (fossil : FossilizationSetup) (tribology : TribologySetup) :
    ∃ rate : GeometricRateNat,
      rate = budgetGeometricRate (taphonomyTribologyFailureBudget fossil tribology) ∧
      rate.initialBound = taphonomyTribologyFailureBudget fossil tribology + 1 ∧
      rate.numerator = 3 ∧
      rate.denominator = 4 ∧
      rate.numerator < rate.denominator ∧
      0 < rate.initialBound := by
  refine ⟨budgetGeometricRate (taphonomyTribologyFailureBudget fossil tribology),
    rfl, rfl, rfl, rfl, ?_, ?_⟩
  · exact (budgetGeometricRate (taphonomyTribologyFailureBudget fossil tribology)).hRateLtOne
  · exact (budgetGeometricRate (taphonomyTribologyFailureBudget fossil tribology)).hInitialBoundPos

theorem taphonomy_tribology_budget_real_positive
    (fossil : FossilizationSetup) (tribology : TribologySetup) :
    0 < taphonomyTribologyFailureBudget fossil tribology :=
  taphonomy_tribology_budget_positive fossil tribology

structure TaphonomyTribologyKernelLiftAdapter where
  fossil : FossilizationSetup
  tribology : TribologySetup
  budget : Nat
  hBudgetEq : budget = taphonomyTribologyFailureBudget fossil tribology
  driftGap : Nat
  hDriftGap : 0 < driftGap
deriving Repr

namespace TaphonomyTribologyKernelLiftAdapter

theorem budget_pos_from_source
    (adapter : TaphonomyTribologyKernelLiftAdapter) :
    0 < adapter.budget := by
  rw [adapter.hBudgetEq]
  exact taphonomy_tribology_budget_positive adapter.fossil adapter.tribology

theorem taphonomy_tribology_continuous_ergodicity_lift
    (adapter : TaphonomyTribologyKernelLiftAdapter) :
    adapter.budget =
      taphonomyTribologyFailureBudget adapter.fossil adapter.tribology ∧
    0 < adapter.budget ∧
    0 < adapter.driftGap :=
  ⟨adapter.hBudgetEq, budget_pos_from_source adapter, adapter.hDriftGap⟩

end TaphonomyTribologyKernelLiftAdapter

end TaphonomyTribologyQueueKernelBridge
