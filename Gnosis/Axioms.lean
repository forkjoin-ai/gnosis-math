import Gnosis.JacksonQueueing
import Gnosis.MeasureQueueing

namespace Gnosis

structure C1C4Model where
  c1ConstraintLocality : Prop
  c2BranchIsolation : Prop
  c3DeterministicFold : Prop
  c4BoundedTermination : Prop
  safety : Prop
  liveness : Prop
  safetyFromC1C2C3 :
    c1ConstraintLocality -> c2BranchIsolation -> c3DeterministicFold -> safety
  livenessFromC4 : c4BoundedTermination -> liveness

theorem c1_c4_imply_safety_and_liveness (model : C1C4Model) :
    model.c1ConstraintLocality ->
    model.c2BranchIsolation ->
    model.c3DeterministicFold ->
    model.c4BoundedTermination ->
    model.safety /\ model.liveness := by
  intro hC1 hC2 hC3 hC4
  exact
    And.intro
      (model.safetyFromC1C2C3 hC1 hC2 hC3)
      (model.livenessFromC4 hC4)

structure QueueContainmentAssumptions where
  beta1 : Nat
  occupancy : Nat
  arrivalRate : Nat
  residenceTime : Nat
  littleLawAtBetaZero : beta1 = 0 -> occupancy = arrivalRate * residenceTime
  topologyControlAtPositiveBeta : 0 < beta1 -> Exists fun controlWidth => 0 < controlWidth

theorem queueing_containment_at_beta1_zero (assumptions : QueueContainmentAssumptions) :
    assumptions.beta1 = 0 ->
    assumptions.occupancy = assumptions.arrivalRate * assumptions.residenceTime := by
  intro hBeta0
  exact assumptions.littleLawAtBetaZero hBeta0

theorem queueing_strict_extension_at_positive_beta (assumptions : QueueContainmentAssumptions) :
    0 < assumptions.beta1 -> Exists fun controlWidth => 0 < controlWidth := by
  intro hPositive
  exact assumptions.topologyControlAtPositiveBeta hPositive

structure QueueLimitAssumptions where
  finiteTruncationsBalanced : Nat -> Prop
  truncationsExhaustSupport : Prop
  monotoneSupportApproximation : Prop
  measurableCustomerTime : Prop
  measurableSojournTime : Prop
  integrableDominatingEnvelope : Prop
  limitBalance : Prop
  limitFromBalancedTruncations :
    truncationsExhaustSupport ->
    monotoneSupportApproximation ->
    measurableCustomerTime ->
    measurableSojournTime ->
    integrableDominatingEnvelope ->
    (∀ n, finiteTruncationsBalanced n) ->
    limitBalance

theorem queue_limit_schema (assumptions : QueueLimitAssumptions) :
    assumptions.truncationsExhaustSupport ->
    assumptions.monotoneSupportApproximation ->
    assumptions.measurableCustomerTime ->
    assumptions.measurableSojournTime ->
    assumptions.integrableDominatingEnvelope ->
    (∀ n, assumptions.finiteTruncationsBalanced n) ->
    assumptions.limitBalance := by
  intro hExhaust hMonotone hCustomer hSojourn hEnvelope hBalanced
  exact assumptions.limitFromBalancedTruncations
    hExhaust
    hMonotone
    hCustomer
    hSojourn
    hEnvelope
    hBalanced

def KernelBridgeWitness {Ω : Type}
    (routingKernel : Ω → Ω → Nat)
    (bridge : Ω) : Prop :=
  (∀ state, 0 < routingKernel state bridge) ∧
    ∀ state, 0 < routingKernel bridge state

def KernelIrreducible {Ω : Type}
    (routingKernel : Ω → Ω → Nat) : Prop :=
  ∃ bridge, KernelBridgeWitness routingKernel bridge

theorem kernelIrreducible_of_bridge
    {Ω : Type}
    (routingKernel : Ω → Ω → Nat)
    (bridge : Ω)
    (hToBridge : ∀ state, 0 < routingKernel state bridge)
    (hFromBridge : ∀ state, 0 < routingKernel bridge state) :
    KernelIrreducible routingKernel := by
  exact ⟨bridge, hToBridge, hFromBridge⟩

def KernelFosterLyapunovDrift {Ω : Type}
    (expectedLyapunov lyapunov : Ω → Nat)
    (smallSet : Ω → Prop)
    (driftGap : Nat) : Prop :=
  ∀ state, ¬ smallSet state → expectedLyapunov state + driftGap ≤ lyapunov state

def KernelPositiveRecurrent {Ω : Type}
    (routingKernel : Ω → Ω → Nat)
    (expectedLyapunov lyapunov : Ω → Nat)
    (smallSet : Ω → Prop)
    (driftGap : Nat) : Prop :=
  KernelIrreducible routingKernel ∧
    KernelFosterLyapunovDrift expectedLyapunov lyapunov smallSet driftGap ∧
    0 < driftGap

structure AdaptiveExpectedLyapunovSynthesis
    (ι Ω : Type) (expectedLyapunov : Ω → Nat) where
  adaptiveTrafficData : AdaptiveJacksonTrafficData ι Ω
  ceilingTrafficData : JacksonTrafficData ι
  ceilingCandidate : ι → Nat
  expectedLift : Ω → (ι → Nat) → Nat
  liftMonotone :
    ∀ state {lhs rhs : ι → Nat},
      (∀ i, lhs i ≤ rhs i) ->
        expectedLift state lhs ≤ expectedLift state rhs

structure AdaptiveSupremumStabilityAssumptions
    (ι Ω : Type) where
  expectedLyapunov : Ω → Nat
  comparison : AdaptiveExpectedLyapunovSynthesis ι Ω expectedLyapunov
  lyapunov : Ω → Nat
  smallSet : Ω → Prop
  driftGap : Nat

structure DagExpressibilityAssumptions where
  finiteDag : Prop
  decompositionExists : Prop
  decompositionSound : Prop
  decompositionComplete : Prop
  encodingFunctionExists : Prop

def DagExpressibleByForkRaceFold (assumptions : DagExpressibilityAssumptions) : Prop :=
  assumptions.decompositionExists /\
  assumptions.decompositionSound /\
  assumptions.decompositionComplete /\
  assumptions.encodingFunctionExists

theorem dag_completeness_schema (assumptions : DagExpressibilityAssumptions) :
    assumptions.finiteDag ->
    assumptions.decompositionExists ->
    assumptions.decompositionSound ->
    assumptions.decompositionComplete ->
    assumptions.encodingFunctionExists ->
    DagExpressibleByForkRaceFold assumptions := by
  intro _ hExists hSound hComplete hEncoding
  exact And.intro hExists (And.intro hSound (And.intro hComplete hEncoding))

structure ParserClosureAssumptions where
  grammarWellFormed : Prop
  tlaCfgPairsComplete : Prop
  parserTotalOnGrammar : Prop
  roundTripStable : Prop

def ParserClosure (assumptions : ParserClosureAssumptions) : Prop :=
  assumptions.grammarWellFormed /\
  assumptions.tlaCfgPairsComplete /\
  assumptions.parserTotalOnGrammar /\
  assumptions.roundTripStable

theorem parser_closure_theorem (assumptions : ParserClosureAssumptions) :
    assumptions.grammarWellFormed ->
    assumptions.tlaCfgPairsComplete ->
    assumptions.parserTotalOnGrammar ->
    assumptions.roundTripStable ->
    ParserClosure assumptions := by
  intro hGrammar hPairs hTotal hRoundTrip
  exact And.intro hGrammar (And.intro hPairs (And.intro hTotal hRoundTrip))

structure ConvergenceAssumptions where
  conservesEnergy : Prop
  irreversibleTime : Prop
  nonzeroGroundOverhead : Prop
  finiteStateModel : Prop
  throughputSelectionPressure : Prop
  forkRaceFoldAttractor : Prop
  noAlternativeInModelClass : Prop

def ConvergenceInModeledClass (assumptions : ConvergenceAssumptions) : Prop :=
  assumptions.forkRaceFoldAttractor /\ assumptions.noAlternativeInModelClass

theorem convergence_schema (assumptions : ConvergenceAssumptions) :
    assumptions.conservesEnergy ->
    assumptions.irreversibleTime ->
    assumptions.nonzeroGroundOverhead ->
    assumptions.finiteStateModel ->
    assumptions.throughputSelectionPressure ->
    assumptions.forkRaceFoldAttractor ->
    assumptions.noAlternativeInModelClass ->
    ConvergenceInModeledClass assumptions := by
  intro _ _ _ _ _ hAttractor hNoAlternative
  exact And.intro hAttractor hNoAlternative

structure InterferenceCoarseningAssumptions where
  fineInitialLive : Nat
  coarseInitialLive : Nat
  coarseTerminalLive : Nat
  coarseTotalVented : Nat
  coarseTotalRepairDebt : Nat
  fineContagious : Prop
  coarseDeterministicCollapse : Prop
  supportPreservingQuotient : 1 < fineInitialLive -> 1 < coarseInitialLive
  survivorFaithfulQuotient : coarseDeterministicCollapse -> coarseTerminalLive = 1
  contagionReflectingQuotient :
    coarseTotalVented = 0 ->
    fineContagious ->
    1 < coarseInitialLive ->
    0 < coarseTotalRepairDebt \/ 1 < coarseTerminalLive

theorem interference_coarsening_zero_vent_requires_repair
    (assumptions : InterferenceCoarseningAssumptions) :
    1 < assumptions.fineInitialLive ->
    assumptions.coarseTotalVented = 0 ->
    assumptions.fineContagious ->
    assumptions.coarseDeterministicCollapse ->
    0 < assumptions.coarseTotalRepairDebt := by
  intro hFineForked hZeroVent hContagious hCollapse
  have hCoarseForked := assumptions.supportPreservingQuotient hFineForked
  have hReflected :=
    assumptions.contagionReflectingQuotient hZeroVent hContagious hCoarseForked
  rcases hReflected with hDebt | hMultiplicity
  · exact hDebt
  · have hSingle := assumptions.survivorFaithfulQuotient hCollapse
    rw [hSingle] at hMultiplicity
    exact absurd hMultiplicity (by decide)

theorem interference_coarsening_schema
    (assumptions : InterferenceCoarseningAssumptions) :
    1 < assumptions.fineInitialLive ->
    assumptions.fineContagious ->
    assumptions.coarseDeterministicCollapse ->
    0 < assumptions.coarseTotalVented \/ 0 < assumptions.coarseTotalRepairDebt := by
  intro hFineForked hContagious hCollapse
  by_cases hZeroVent : assumptions.coarseTotalVented = 0
  · right
    exact
      interference_coarsening_zero_vent_requires_repair
        assumptions
        hFineForked
        hZeroVent
        hContagious
        hCollapse
  · left
    exact Nat.pos_of_ne_zero hZeroVent

abbrev Bu := Nat

structure BeautyDefinitionAssumptions where
  intrinsicBu : Bu
  implementationBuA : Bu
  implementationBuB : Bu
  deficitBuA : Bu
  deficitBuB : Bu
  beautyBuA : Bu
  beautyBuB : Bu
  deficitDefA : deficitBuA = intrinsicBu - implementationBuA
  deficitDefB : deficitBuB = intrinsicBu - implementationBuB
  beautyDefA : beautyBuA = intrinsicBu - deficitBuA
  beautyDefB : beautyBuB = intrinsicBu - deficitBuB

theorem beauty_definition_schema (assumptions : BeautyDefinitionAssumptions) :
    assumptions.deficitBuA = assumptions.intrinsicBu - assumptions.implementationBuA /\
    assumptions.deficitBuB = assumptions.intrinsicBu - assumptions.implementationBuB /\
    assumptions.beautyBuA = assumptions.intrinsicBu - assumptions.deficitBuA /\
    assumptions.beautyBuB = assumptions.intrinsicBu - assumptions.deficitBuB := by
  exact And.intro assumptions.deficitDefA (And.intro assumptions.deficitDefB
    (And.intro assumptions.beautyDefA assumptions.beautyDefB))

structure BeautyLatencyMonotonicityAssumptions where
  deficitBuA : Bu
  deficitBuB : Bu
  latencyA : Nat
  latencyB : Nat
  deficitOrder : deficitBuA <= deficitBuB
  latencyMonotoneFromDeficit : deficitBuA <= deficitBuB -> latencyA <= latencyB

theorem beauty_latency_monotone_schema (assumptions : BeautyLatencyMonotonicityAssumptions) :
    assumptions.latencyA <= assumptions.latencyB := by
  exact assumptions.latencyMonotoneFromDeficit assumptions.deficitOrder

structure BeautyWasteMonotonicityAssumptions where
  deficitBuA : Bu
  deficitBuB : Bu
  wasteA : Nat
  wasteB : Nat
  deficitOrder : deficitBuA <= deficitBuB
  wasteMonotoneFromDeficit : deficitBuA <= deficitBuB -> wasteA <= wasteB

theorem beauty_waste_monotone_schema (assumptions : BeautyWasteMonotonicityAssumptions) :
    assumptions.wasteA <= assumptions.wasteB := by
  exact assumptions.wasteMonotoneFromDeficit assumptions.deficitOrder

structure BeautyParetoAssumptions where
  deficitBuA : Bu
  deficitBuB : Bu
  latencyA : Nat
  latencyB : Nat
  wasteA : Nat
  wasteB : Nat
  zeroDeficitA : deficitBuA = 0
  deficitOrder : deficitBuA <= deficitBuB
  latencyMonotoneFromDeficit : deficitBuA <= deficitBuB -> latencyA <= latencyB
  wasteMonotoneFromDeficit : deficitBuA <= deficitBuB -> wasteA <= wasteB

theorem beauty_pareto_optimality_schema (assumptions : BeautyParetoAssumptions) :
    assumptions.latencyA <= assumptions.latencyB /\
    assumptions.wasteA <= assumptions.wasteB := by
  constructor
  · exact assumptions.latencyMonotoneFromDeficit assumptions.deficitOrder
  · exact assumptions.wasteMonotoneFromDeficit assumptions.deficitOrder

structure BeautyCompositionAssumptions where
  pipelineBu : Bu
  protocolBu : Bu
  compressionBu : Bu
  globalBu : Bu
  additiveComposition : globalBu = pipelineBu + protocolBu + compressionBu

theorem beauty_composition_schema (assumptions : BeautyCompositionAssumptions) :
    assumptions.globalBu =
      assumptions.pipelineBu + assumptions.protocolBu + assumptions.compressionBu := by
  exact assumptions.additiveComposition

structure BeautyOptimalityAssumptions where
  definition : BeautyDefinitionAssumptions
  latency : BeautyLatencyMonotonicityAssumptions
  waste : BeautyWasteMonotonicityAssumptions
  pareto : BeautyParetoAssumptions
  composition : BeautyCompositionAssumptions
  beautyMonotoneFromDeficit :
    latency.deficitBuA <= latency.deficitBuB ->
      definition.beautyBuB <= definition.beautyBuA

theorem beauty_optimality_schema (assumptions : BeautyOptimalityAssumptions) :
    (assumptions.definition.deficitBuA =
      assumptions.definition.intrinsicBu - assumptions.definition.implementationBuA /\
     assumptions.definition.deficitBuB =
      assumptions.definition.intrinsicBu - assumptions.definition.implementationBuB /\
     assumptions.definition.beautyBuA =
      assumptions.definition.intrinsicBu - assumptions.definition.deficitBuA /\
     assumptions.definition.beautyBuB =
      assumptions.definition.intrinsicBu - assumptions.definition.deficitBuB) /\
    assumptions.latency.latencyA <= assumptions.latency.latencyB /\
    assumptions.waste.wasteA <= assumptions.waste.wasteB /\
    assumptions.pareto.latencyA <= assumptions.pareto.latencyB /\
    assumptions.pareto.wasteA <= assumptions.pareto.wasteB /\
    assumptions.definition.beautyBuB <= assumptions.definition.beautyBuA /\
    assumptions.composition.globalBu =
      assumptions.composition.pipelineBu + assumptions.composition.protocolBu +
      assumptions.composition.compressionBu := by
  refine And.intro (beauty_definition_schema assumptions.definition) ?_
  refine And.intro (beauty_latency_monotone_schema assumptions.latency) ?_
  refine And.intro (beauty_waste_monotone_schema assumptions.waste) ?_
  refine And.intro (beauty_pareto_optimality_schema assumptions.pareto).1 ?_
  refine And.intro (beauty_pareto_optimality_schema assumptions.pareto).2 ?_
  refine And.intro
    (assumptions.beautyMonotoneFromDeficit assumptions.latency.deficitOrder)
    (beauty_composition_schema assumptions.composition)

end Gnosis