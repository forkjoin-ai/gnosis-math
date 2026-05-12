import Init
import Gnosis.GeometricErgodicity

/-!
# Media/Conversion/Knapsack Queue Kernel Bridge

Finite clickbait, conversion-vent, and viewport-overlap witnesses for stale
MCP rows.
-/

namespace MediaConversionKnapsackQueueKernelBridge

structure MediaSetup where
  baseline : Nat
  clickstr : Nat
  cognitiveStrand : Nat
  hClick : 1 ≤ clickstr
  hCognitive : cognitiveStrand = baseline + clickstr
deriving Repr

structure ConversionSetup where
  uiFriction : Nat
  buleInvestment : Nat
  ventSlam : Nat
  hAbandon : buleInvestment < uiFriction
  hVent : ventSlam = uiFriction - buleInvestment
deriving Repr

structure KnapsackSetup where
  screenCapacity : Nat
  visualOverlap : Nat
  pleromicData : Nat
  hOverlap : 1 ≤ visualOverlap
  hPleromic : pleromicData = screenCapacity + visualOverlap
deriving Repr

def conversionVentFailureBudget (conversion : ConversionSetup) : Nat :=
  conversion.ventSlam

def mediaConversionKnapsackFailureBudget
    (media : MediaSetup)
    (conversion : ConversionSetup)
    (knapsack : KnapsackSetup) : Nat :=
  media.clickstr + conversionVentFailureBudget conversion + knapsack.visualOverlap

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

theorem conversion_vent_positive
    (conversion : ConversionSetup) :
    0 < conversionVentFailureBudget conversion := by
  unfold conversionVentFailureBudget
  rw [conversion.hVent]
  exact Nat.sub_pos_of_lt conversion.hAbandon

theorem media_conversion_knapsack_budget_positive
    (media : MediaSetup)
    (conversion : ConversionSetup)
    (knapsack : KnapsackSetup) :
    0 < mediaConversionKnapsackFailureBudget media conversion knapsack := by
  unfold mediaConversionKnapsackFailureBudget
  rw [Nat.add_assoc]
  exact Nat.lt_add_right
    (conversionVentFailureBudget conversion + knapsack.visualOverlap)
    media.hClick

theorem media_conversion_knapsack_budget_yields_unit_queue_boundary
    (media : MediaSetup)
    (conversion : ConversionSetup)
    (knapsack : KnapsackSetup) :
    media.cognitiveStrand = media.baseline + media.clickstr ∧
    0 < media.clickstr ∧
    conversion.ventSlam = conversion.uiFriction - conversion.buleInvestment ∧
    0 < conversionVentFailureBudget conversion ∧
    knapsack.pleromicData = knapsack.screenCapacity + knapsack.visualOverlap ∧
    0 < knapsack.visualOverlap ∧
    0 < mediaConversionKnapsackFailureBudget media conversion knapsack ∧
    ∃ boundary : QueueBoundaryWitnessNat,
      boundary.beta1 = 0 ∧
      boundary.capacity = 1 ∧
      boundary.arrivalRate =
        mediaConversionKnapsackFailureBudget media conversion knapsack ∧
      boundary.serviceRate =
        quorumSize
          (replicaCount
            (mediaConversionKnapsackFailureBudget media conversion knapsack))
          (mediaConversionKnapsackFailureBudget media conversion knapsack) := by
  exact ⟨media.hCognitive, media.hClick, conversion.hVent,
    conversion_vent_positive conversion, knapsack.hPleromic, knapsack.hOverlap,
    media_conversion_knapsack_budget_positive media conversion knapsack,
    ⟨canonicalQueueBoundary
      (mediaConversionKnapsackFailureBudget media conversion knapsack),
      rfl, rfl, rfl, rfl⟩⟩

theorem media_conversion_knapsack_budget_yields_positive_topological_deficit
    (media : MediaSetup)
    (conversion : ConversionSetup)
    (knapsack : KnapsackSetup) :
    0 < topologicalDeficit
      (mediaConversionKnapsackFailureBudget media conversion knapsack + 1) 1 := by
  unfold topologicalDeficit
  rw [Nat.add_sub_cancel]
  exact media_conversion_knapsack_budget_positive media conversion knapsack

theorem media_conversion_knapsack_budget_does_not_force_two_step_service_surplus
    (media : MediaSetup)
    (conversion : ConversionSetup)
    (knapsack : KnapsackSetup) :
    ¬ (∀ boundary : QueueBoundaryWitnessNat,
        boundary.arrivalRate =
          mediaConversionKnapsackFailureBudget media conversion knapsack →
        boundary.serviceRate =
          quorumSize
            (replicaCount
              (mediaConversionKnapsackFailureBudget media conversion knapsack))
            (mediaConversionKnapsackFailureBudget media conversion knapsack) →
        boundary.arrivalRate + 2 ≤ boundary.serviceRate) := by
  intro hAll
  let budget := mediaConversionKnapsackFailureBudget media conversion knapsack
  let boundary := canonicalQueueBoundary budget
  have hSurplus : budget + 2 ≤ budget + 1 := hAll boundary rfl rfl
  exact (Nat.not_succ_le_self (budget + 1)) hSurplus

theorem media_conversion_knapsack_budget_yields_geometric_rate_certificate
    (media : MediaSetup)
    (conversion : ConversionSetup)
    (knapsack : KnapsackSetup) :
    ∃ rate : GeometricRateNat,
      rate = budgetGeometricRate
        (mediaConversionKnapsackFailureBudget media conversion knapsack) ∧
      rate.initialBound =
        mediaConversionKnapsackFailureBudget media conversion knapsack + 1 ∧
      rate.numerator = 3 ∧
      rate.denominator = 4 ∧
      rate.numerator < rate.denominator ∧
      0 < rate.initialBound := by
  refine ⟨budgetGeometricRate
      (mediaConversionKnapsackFailureBudget media conversion knapsack),
    rfl, rfl, rfl, rfl, ?_, ?_⟩
  · exact (budgetGeometricRate
      (mediaConversionKnapsackFailureBudget media conversion knapsack)).hRateLtOne
  · exact (budgetGeometricRate
      (mediaConversionKnapsackFailureBudget media conversion knapsack)).hInitialBoundPos

structure MediaConversionKnapsackKernelLiftAdapter where
  media : MediaSetup
  conversion : ConversionSetup
  knapsack : KnapsackSetup
  budget : Nat
  hBudgetEq :
    budget = mediaConversionKnapsackFailureBudget media conversion knapsack
deriving Repr

namespace MediaConversionKnapsackKernelLiftAdapter

theorem budget_pos_from_source
    (adapter : MediaConversionKnapsackKernelLiftAdapter) :
    0 < adapter.budget := by
  rw [adapter.hBudgetEq]
  exact media_conversion_knapsack_budget_positive
    adapter.media adapter.conversion adapter.knapsack

theorem media_conversion_knapsack_continuous_ergodicity_lift
    {Ω : Type}
    {maxQueue : Nat}
    (adapter : MediaConversionKnapsackKernelLiftAdapter)
    (embedding : Gnosis.DiscreteSubLatticeEmbedding Ω maxQueue)
    (witness : Gnosis.GeometricErgodicWitness maxQueue)
    (hKernelMatch : witness.envelope.kernel = embedding.discreteKernel) :
    0 < adapter.budget ∧
    adapter.media.cognitiveStrand =
      adapter.media.baseline + adapter.media.clickstr ∧
    adapter.conversion.ventSlam =
      adapter.conversion.uiFriction - adapter.conversion.buleInvestment ∧
    adapter.knapsack.pleromicData =
      adapter.knapsack.screenCapacity + adapter.knapsack.visualOverlap ∧
    embedding.continuousKernel.fosterDrift ∧
    0 < embedding.continuousKernel.driftGap ∧
    witness.rate.rateNumerator < witness.rate.rateDenominator := by
  have hLift :=
    Gnosis.continuous_ergodicity_lift embedding witness hKernelMatch
  exact ⟨adapter.budget_pos_from_source, adapter.media.hCognitive,
    adapter.conversion.hVent, adapter.knapsack.hPleromic,
    hLift.1, hLift.2.1, hLift.2.2⟩

end MediaConversionKnapsackKernelLiftAdapter

end MediaConversionKnapsackQueueKernelBridge
