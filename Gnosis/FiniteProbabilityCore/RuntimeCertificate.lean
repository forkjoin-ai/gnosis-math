import Gnosis.FiniteProbabilityCore.Interfaces

namespace Gnosis
namespace FiniteProbabilityCore

/-!
# Runtime Probability Certificates

Compact certificate records for mirroring finite probability accounting in
runtime systems. These records intentionally expose only natural-number fields:
runtime code can validate arithmetic cheaply, while Lean keeps the same
invariants available as the native process, kernel, cover, and
completed-interface structures.
-/

structure RuntimeProbabilityResidual where
  unobservedMass : Nat
  truncatedMass : Nat
  coarseningDebt : Nat
  deriving Repr, DecidableEq

def RuntimeProbabilityResidual.total
    (residual : RuntimeProbabilityResidual) : Nat :=
  residual.unobservedMass + residual.truncatedMass + residual.coarseningDebt

def RuntimeProbabilityResidual.toState
    (residual : RuntimeProbabilityResidual) : ProbabilityResidualState :=
  { unobservedMass := residual.unobservedMass
    truncatedMass := residual.truncatedMass
    coarseningDebt := residual.coarseningDebt }

theorem runtime_probability_residual_total_eq_state
    (residual : RuntimeProbabilityResidual) :
    probabilityResidual residual.toState () = residual.total := by
  simp [RuntimeProbabilityResidual.toState,
    RuntimeProbabilityResidual.total, probabilityResidual]

structure RuntimeProbabilityProcessCertificate where
  inputMass : Nat
  outputMass : Nat
  massLoss : Nat
  residual : RuntimeProbabilityResidual
  balance : outputMass + massLoss = inputMass
  lossCovered : massLoss ≤ residual.total
  deriving Repr

def RuntimeProbabilityProcessCertificate.residualState
    (certificate : RuntimeProbabilityProcessCertificate) :
    ProbabilityResidualState :=
  certificate.residual.toState

theorem runtime_process_certificate_no_hidden_defect
    (certificate : RuntimeProbabilityProcessCertificate)
    (budget wider : Nat)
    (observer : ScalarObserver)
    (depth : Nat)
    (hresidual : certificate.residual.total ≤ budget)
    (hcovers : ObserverBudgetCovers natBudgetMeasure budget wider)
    (hbudget : wider ≤ depth) :
    natResidualSignature.answer
      (probabilityObserverPromotion.promote
        certificate.residualState ())
      observer depth := by
  apply probability_no_hidden_defect
  · rwa [RuntimeProbabilityProcessCertificate.residualState,
      runtime_probability_residual_total_eq_state]
  · exact hcovers
  · exact hbudget

def RuntimeProbabilityProcessCertificate.toProcess
    (certificate : RuntimeProbabilityProcessCertificate)
    (hinput : 0 < certificate.inputMass)
    (houtput : 0 < certificate.outputMass) :
    FiniteProbabilityProcess :=
  { input := singletonDistribution certificate.inputMass hinput
    output := singletonDistribution
      certificate.outputMass
      houtput
    massLoss := certificate.massLoss
    residual := certificate.residual.total
    balance := by
      rw [singleton_distribution_total_mass]
      rw [singleton_distribution_total_mass]
      exact certificate.balance
    lossCovered := certificate.lossCovered }

structure RuntimeProbabilityKernelCertificate where
  inputMass : Nat
  outputMass : Nat
  lostMass : Nat
  balance : outputMass + lostMass = inputMass
  deriving Repr

theorem runtime_kernel_certificate_output_le_input
    (certificate : RuntimeProbabilityKernelCertificate) :
    certificate.outputMass ≤ certificate.inputMass := by
  rw [← certificate.balance]
  exact Nat.le_add_right certificate.outputMass certificate.lostMass

structure RuntimeProbabilityCoverCertificate where
  footprint : Nat
  shadow : Nat
  horizonDepth : Nat
  horizonResidualBudget : Nat
  footprintBounded : footprint ≤ horizonDepth
  shadowBounded : shadow ≤ horizonResidualBudget
  deriving Repr

def RuntimeProbabilityCoverCertificate.toFiniteCover
    (certificate : RuntimeProbabilityCoverCertificate) : FiniteCover :=
  { footprint := certificate.footprint
    shadow := certificate.shadow
    horizon :=
      { depth := certificate.horizonDepth
        residualBudget := certificate.horizonResidualBudget }
    footprintBounded := certificate.footprintBounded
    shadowBounded := certificate.shadowBounded }

theorem runtime_cover_certificate_no_hidden_defect
    (certificate : RuntimeProbabilityCoverCertificate)
    (wider : Nat)
    (observer : ScalarObserver)
    (depth : Nat)
    (hcovers :
      ObserverBudgetCovers natBudgetMeasure
        certificate.horizonResidualBudget wider)
    (hbudget : wider ≤ depth) :
    natResidualSignature.answer
      (probabilityObserverPromotion.promote
        { unobservedMass := certificate.shadow,
          truncatedMass := 0,
          coarseningDebt := 0 } ())
      observer depth :=
  finite_cover_no_hidden_defect
    certificate.toFiniteCover wider observer depth hcovers hbudget

structure RuntimeCompletedInterfaceCertificate where
  visibleDepth : Nat
  shadow : Nat
  horizonDepth : Nat
  horizonResidualBudget : Nat
  depthWithinHorizon : visibleDepth ≤ horizonDepth
  shadowWithinHorizon : shadow ≤ horizonResidualBudget
  deriving Repr

def RuntimeCompletedInterfaceCertificate.toCover
    (certificate : RuntimeCompletedInterfaceCertificate) :
    RuntimeProbabilityCoverCertificate :=
  { footprint := certificate.visibleDepth
    shadow := certificate.shadow
    horizonDepth := certificate.horizonDepth
    horizonResidualBudget := certificate.horizonResidualBudget
    footprintBounded := certificate.depthWithinHorizon
    shadowBounded := certificate.shadowWithinHorizon }

theorem runtime_completed_interface_certificate_no_hidden_defect
    (certificate : RuntimeCompletedInterfaceCertificate)
    (wider : Nat)
    (observer : ScalarObserver)
    (depth : Nat)
    (hcovers :
      ObserverBudgetCovers natBudgetMeasure
        certificate.horizonResidualBudget wider)
    (hbudget : wider ≤ depth) :
    natResidualSignature.answer
      (probabilityObserverPromotion.promote
        { unobservedMass := certificate.shadow,
          truncatedMass := 0,
          coarseningDebt := 0 } ())
      observer depth :=
  runtime_cover_certificate_no_hidden_defect
    certificate.toCover wider observer depth hcovers hbudget

/-! ## Runtime topology probability theorem mirrors -/

inductive RuntimeTopologyEvent where
  | fork (branchCount : Nat)
  | race (branchCount : Nat)
  | fold
  | vent
  | observe
  deriving Repr, DecidableEq

def RuntimeTopologyEvent.residual : RuntimeTopologyEvent → Nat
  | .fork _ => 0
  | .race branchCount => branchCount - 1
  | .fold => 1
  | .vent => 1
  | .observe => 0

def runtimeTopologyEventResidual : List RuntimeTopologyEvent → Nat
  | [] => 0
  | event :: rest => event.residual + runtimeTopologyEventResidual rest

structure RuntimeTopologyProbabilityCertificate where
  events : List RuntimeTopologyEvent
  visibleMass : Nat
  positiveVisibleMass : 0 < visibleMass
  chainResidual : Nat
  residualAccounts : chainResidual = runtimeTopologyEventResidual events
  deriving Repr

structure TopologyResidualTheoremWitness where
  chainResidual : Nat
  eventResidualSum : Nat
  equalityHolds : chainResidual = eventResidualSum
  deriving Repr

def witnessTopologyResidualTheorem
    (certificate : RuntimeTopologyProbabilityCertificate) :
    TopologyResidualTheoremWitness :=
  { chainResidual := certificate.chainResidual
    eventResidualSum := runtimeTopologyEventResidual certificate.events
    equalityHolds := certificate.residualAccounts }

theorem witness_topology_residual_theorem_sound
    (certificate : RuntimeTopologyProbabilityCertificate) :
    (witnessTopologyResidualTheorem certificate).chainResidual =
      (witnessTopologyResidualTheorem certificate).eventResidualSum :=
  (witnessTopologyResidualTheorem certificate).equalityHolds

structure PositiveVisibleMassWitness where
  inputMass : Nat
  outputMass : Nat
  positiveInput : 0 < inputMass
  positiveOutput : 0 < outputMass
  deriving Repr

def witnessPositiveVisibleMass
    (certificate : RuntimeTopologyProbabilityCertificate) :
    PositiveVisibleMassWitness :=
  { inputMass := certificate.visibleMass
    outputMass := certificate.visibleMass
    positiveInput := certificate.positiveVisibleMass
    positiveOutput := certificate.positiveVisibleMass }

structure RuntimeCheckerTopologyStats where
  forkCount : Nat
  foldCount : Nat
  ventCount : Nat
  deriving Repr, DecidableEq

def RuntimeCheckerTopologyStats.events
    (stats : RuntimeCheckerTopologyStats) : List RuntimeTopologyEvent :=
  List.replicate stats.forkCount (RuntimeTopologyEvent.fork 2) ++
    List.replicate stats.foldCount RuntimeTopologyEvent.fold ++
    List.replicate stats.ventCount RuntimeTopologyEvent.vent ++
    [RuntimeTopologyEvent.observe]

def RuntimeCheckerTopologyStats.shadow
    (stats : RuntimeCheckerTopologyStats) : Nat :=
  stats.foldCount + stats.ventCount

theorem runtime_topology_replicate_fork_residual_zero
    (count : Nat) :
    runtimeTopologyEventResidual
      (List.replicate count (RuntimeTopologyEvent.fork 2)) = 0 := by
  induction count with
  | zero => simp [runtimeTopologyEventResidual]
  | succ count ih =>
      simp [List.replicate, runtimeTopologyEventResidual, ih,
        RuntimeTopologyEvent.residual]

theorem runtime_topology_replicate_fold_residual
    (count : Nat) :
    runtimeTopologyEventResidual
      (List.replicate count RuntimeTopologyEvent.fold) = count := by
  induction count with
  | zero => simp [runtimeTopologyEventResidual]
  | succ count ih =>
      simp [List.replicate, runtimeTopologyEventResidual, ih,
        RuntimeTopologyEvent.residual]
      exact Nat.add_comm 1 count

theorem runtime_topology_replicate_vent_residual
    (count : Nat) :
    runtimeTopologyEventResidual
      (List.replicate count RuntimeTopologyEvent.vent) = count := by
  induction count with
  | zero => simp [runtimeTopologyEventResidual]
  | succ count ih =>
      simp [List.replicate, runtimeTopologyEventResidual, ih,
        RuntimeTopologyEvent.residual]
      exact Nat.add_comm 1 count

theorem runtime_topology_event_residual_append
    (left right : List RuntimeTopologyEvent) :
    runtimeTopologyEventResidual (left ++ right) =
      runtimeTopologyEventResidual left + runtimeTopologyEventResidual right := by
  induction left with
  | nil => simp [runtimeTopologyEventResidual]
  | cons event rest ih =>
      simp [runtimeTopologyEventResidual, ih, Nat.add_assoc]

theorem runtime_checker_topology_events_shadow
    (stats : RuntimeCheckerTopologyStats) :
    runtimeTopologyEventResidual stats.events = stats.shadow := by
  unfold RuntimeCheckerTopologyStats.events RuntimeCheckerTopologyStats.shadow
  rw [runtime_topology_event_residual_append]
  rw [runtime_topology_event_residual_append]
  rw [runtime_topology_event_residual_append]
  simp [runtime_topology_replicate_fork_residual_zero,
    runtime_topology_replicate_fold_residual,
    runtime_topology_replicate_vent_residual,
    runtimeTopologyEventResidual, RuntimeTopologyEvent.residual]

def RuntimeCheckerTopologyStats.toCertificate
    (stats : RuntimeCheckerTopologyStats) :
    RuntimeTopologyProbabilityCertificate :=
  { events := stats.events
    visibleMass := 1
    positiveVisibleMass := Nat.succ_pos 0
    chainResidual := stats.shadow
    residualAccounts := by
      rw [runtime_checker_topology_events_shadow] }

structure CheckerTopologyCompactnessWitness where
  foldVentResidual : Nat
  checkerShadow : Nat
  equalityHolds : checkerShadow = foldVentResidual
  deriving Repr

def witnessCheckerTopologyCompactness
    (stats : RuntimeCheckerTopologyStats) :
    CheckerTopologyCompactnessWitness :=
  { foldVentResidual := stats.foldCount + stats.ventCount
    checkerShadow := (RuntimeCheckerTopologyStats.toCertificate stats).chainResidual
    equalityHolds := rfl }

theorem witness_checker_topology_compactness_sound
    (stats : RuntimeCheckerTopologyStats) :
    (witnessCheckerTopologyCompactness stats).checkerShadow =
      (witnessCheckerTopologyCompactness stats).foldVentResidual :=
  (witnessCheckerTopologyCompactness stats).equalityHolds

structure ObserverAcceptanceWitness where
  observerBudget : Nat
  residual : Nat
  accepts : residual ≤ observerBudget
  deriving Repr

def witnessObserverAcceptance
    (certificate : RuntimeTopologyProbabilityCertificate)
    (observerBudget : Nat)
    (haccepts : certificate.chainResidual ≤ observerBudget) :
    ObserverAcceptanceWitness :=
  { observerBudget := observerBudget
    residual := certificate.chainResidual
    accepts := haccepts }

structure TopologyShadowEquivalenceWitness where
  leftResidual : Nat
  rightResidual : Nat
  residualDifference : Nat
  observerBudget : Nat
  equivalent : residualDifference ≤ observerBudget
  deriving Repr

def witnessTopologyShadowEquivalence
    (left right : RuntimeTopologyProbabilityCertificate)
    (observerBudget : Nat)
    (hequivalent :
      natAbsDiff left.chainResidual right.chainResidual ≤ observerBudget) :
    TopologyShadowEquivalenceWitness :=
  { leftResidual := left.chainResidual
    rightResidual := right.chainResidual
    residualDifference := natAbsDiff left.chainResidual right.chainResidual
    observerBudget := observerBudget
    equivalent := hequivalent }

/-! ## Generic bounded witness pattern -/

structure RuntimeBoundedWitnessCertificate where
  observedSurface : Nat
  residualShadow : Nat
  observerBudget : Nat
  theoremWitness : Nat
  accepted : residualShadow ≤ observerBudget
  deriving Repr

def RuntimeTopologyProbabilityCertificate.toBoundedWitness
    (certificate : RuntimeTopologyProbabilityCertificate)
    (observerBudget : Nat)
    (haccepted : certificate.chainResidual ≤ observerBudget) :
    RuntimeBoundedWitnessCertificate :=
  { observedSurface := certificate.visibleMass
    residualShadow := certificate.chainResidual
    observerBudget := observerBudget
    theoremWitness := runtimeTopologyEventResidual certificate.events
    accepted := haccepted }

theorem runtime_bounded_witness_shadow_covered
    (certificate : RuntimeBoundedWitnessCertificate) :
    certificate.residualShadow ≤ certificate.observerBudget :=
  certificate.accepted

structure RuntimeBoundedWitnessEquivalence where
  leftResidual : Nat
  rightResidual : Nat
  residualDifference : Nat
  observerBudget : Nat
  equivalent : residualDifference ≤ observerBudget
  deriving Repr

def witnessBoundedEquivalence
    (left right : RuntimeBoundedWitnessCertificate)
    (observerBudget : Nat)
    (hequivalent :
      natAbsDiff left.residualShadow right.residualShadow ≤ observerBudget) :
    RuntimeBoundedWitnessEquivalence :=
  { leftResidual := left.residualShadow
    rightResidual := right.residualShadow
    residualDifference := natAbsDiff left.residualShadow right.residualShadow
    observerBudget := observerBudget
    equivalent := hequivalent }

def runtimeBoundedWitnessPipelineResidual :
    List RuntimeBoundedWitnessCertificate → Nat
  | [] => 0
  | witness :: rest =>
      witness.residualShadow + runtimeBoundedWitnessPipelineResidual rest

theorem runtime_bounded_witness_pipeline_residual_append
    (left right : List RuntimeBoundedWitnessCertificate) :
    runtimeBoundedWitnessPipelineResidual (left ++ right) =
      runtimeBoundedWitnessPipelineResidual left +
        runtimeBoundedWitnessPipelineResidual right := by
  induction left with
  | nil => simp [runtimeBoundedWitnessPipelineResidual]
  | cons witness rest ih =>
      simp [runtimeBoundedWitnessPipelineResidual, ih, Nat.add_assoc]

structure RuntimeBoundedWitnessPipeline where
  witnesses : List RuntimeBoundedWitnessCertificate
  residualShadow : Nat
  observerBudget : Nat
  residualAccounts :
    residualShadow = runtimeBoundedWitnessPipelineResidual witnesses
  accepted : residualShadow ≤ observerBudget
  deriving Repr

theorem runtime_bounded_witness_pipeline_shadow_covered
    (pipeline : RuntimeBoundedWitnessPipeline) :
    pipeline.residualShadow ≤ pipeline.observerBudget :=
  pipeline.accepted

structure RuntimeBoundedWitnessPipelineTheorem where
  residualShadow : Nat
  witnessResidualSum : Nat
  equalityHolds : residualShadow = witnessResidualSum
  deriving Repr

def witnessBoundedPipelineTheorem
    (pipeline : RuntimeBoundedWitnessPipeline) :
    RuntimeBoundedWitnessPipelineTheorem :=
  { residualShadow := pipeline.residualShadow
    witnessResidualSum :=
      runtimeBoundedWitnessPipelineResidual pipeline.witnesses
    equalityHolds := pipeline.residualAccounts }

theorem witness_bounded_pipeline_theorem_sound
    (pipeline : RuntimeBoundedWitnessPipeline) :
    (witnessBoundedPipelineTheorem pipeline).residualShadow =
      (witnessBoundedPipelineTheorem pipeline).witnessResidualSum :=
  (witnessBoundedPipelineTheorem pipeline).equalityHolds

def RuntimeBoundedWitnessPipeline.toProcessChain
    (pipeline : RuntimeBoundedWitnessPipeline) :
    FiniteProbabilityProcessChain :=
  let distribution := singletonDistribution 1 (Nat.succ_pos 0)
  let process : FiniteProbabilityProcess :=
    { input := distribution
      output := distribution
      massLoss := 0
      residual := pipeline.residualShadow
      balance := by simp
      lossCovered := Nat.zero_le pipeline.residualShadow }
  { input := singletonDistribution 1 (Nat.succ_pos 0)
    output := singletonDistribution 1 (Nat.succ_pos 0)
    processes := [process]
    massLoss := 0
    residual := pipeline.residualShadow
    balance := by simp [singleton_distribution_total_mass]
    massLossAccounts := by simp [processListMassLoss, process]
    residualAccounts := by simp [processListResidual, process] }

theorem runtime_bounded_witness_pipeline_process_chain_residual
    (pipeline : RuntimeBoundedWitnessPipeline) :
    pipeline.toProcessChain.residual = pipeline.residualShadow :=
  rfl

theorem runtime_bounded_witness_pipeline_process_chain_no_hidden_defect
    (pipeline : RuntimeBoundedWitnessPipeline)
    (wider : Nat)
    (observer : ScalarObserver)
    (depth : Nat)
    (hcovers :
      ObserverBudgetCovers natBudgetMeasure pipeline.observerBudget wider)
    (hbudget : wider ≤ depth) :
    natResidualSignature.answer
      (probabilityObserverPromotion.promote
        pipeline.toProcessChain.residualState ())
      observer depth :=
  process_chain_no_hidden_defect
    pipeline.toProcessChain pipeline.observerBudget wider observer depth
    (by
      rw [runtime_bounded_witness_pipeline_process_chain_residual]
      exact pipeline.accepted)
    hcovers hbudget

/-! ## Domain bounded-witness adapters -/

structure BoundedWitnessAdapter (State : Type) where
  domainName : String
  residual : State → Nat

def BoundedWitnessAdapter.toWitness
    {State : Type}
    (adapter : BoundedWitnessAdapter State)
    (observedSurface : Nat)
    (state : State)
    (observerBudget : Nat)
    (haccepted : adapter.residual state ≤ observerBudget) :
    RuntimeBoundedWitnessCertificate :=
  { observedSurface := observedSurface
    residualShadow := adapter.residual state
    observerBudget := observerBudget
    theoremWitness := adapter.residual state
    accepted := haccepted }

theorem bounded_witness_adapter_shadow_covered
    {State : Type}
    (adapter : BoundedWitnessAdapter State)
    (observedSurface : Nat)
    (state : State)
    (observerBudget : Nat)
    (haccepted : adapter.residual state ≤ observerBudget) :
    (adapter.toWitness observedSurface state observerBudget haccepted).residualShadow ≤
      (adapter.toWitness observedSurface state observerBudget haccepted).observerBudget :=
  runtime_bounded_witness_shadow_covered
    (adapter.toWitness observedSurface state observerBudget haccepted)

def queueBoundedWitnessAdapter :
    BoundedWitnessAdapter QueueResidualState :=
  { domainName := "queue"
    residual := fun state => queueResidual state () }

def thermodynamicBoundedWitnessAdapter :
    BoundedWitnessAdapter ThermodynamicResidualState :=
  { domainName := "thermodynamic"
    residual := fun state => thermodynamicResidual state () }

def meshRoutingBoundedWitnessAdapter :
    BoundedWitnessAdapter MeshRoutingResidualState :=
  { domainName := "mesh-routing"
    residual := fun state => meshRoutingResidual state () }

def attentionBoundedWitnessAdapter :
    BoundedWitnessAdapter AttentionResidualState :=
  { domainName := "attention"
    residual := fun state => attentionResidual state () }

def finiteApproximationBoundedWitnessAdapter :
    BoundedWitnessAdapter FiniteApproximationResidualState :=
  { domainName := "finite-approximation"
    residual := fun state => finiteApproximationResidual state () }

def queueBoundedWitness
    (observedSurface : Nat)
    (state : QueueResidualState)
    (observerBudget : Nat)
    (haccepted : queueResidual state () ≤ observerBudget) :
    RuntimeBoundedWitnessCertificate :=
  queueBoundedWitnessAdapter.toWitness
    observedSurface state observerBudget haccepted

theorem queue_bounded_witness_shadow_covered
    (observedSurface : Nat)
    (state : QueueResidualState)
    (observerBudget : Nat)
    (haccepted : queueResidual state () ≤ observerBudget) :
    (queueBoundedWitness observedSurface state observerBudget haccepted).residualShadow ≤
      (queueBoundedWitness observedSurface state observerBudget haccepted).observerBudget :=
  runtime_bounded_witness_shadow_covered
    (queueBoundedWitness observedSurface state observerBudget haccepted)

def thermodynamicBoundedWitness
    (observedSurface : Nat)
    (state : ThermodynamicResidualState)
    (observerBudget : Nat)
    (haccepted : thermodynamicResidual state () ≤ observerBudget) :
    RuntimeBoundedWitnessCertificate :=
  thermodynamicBoundedWitnessAdapter.toWitness
    observedSurface state observerBudget haccepted

theorem thermodynamic_bounded_witness_shadow_covered
    (observedSurface : Nat)
    (state : ThermodynamicResidualState)
    (observerBudget : Nat)
    (haccepted : thermodynamicResidual state () ≤ observerBudget) :
    (thermodynamicBoundedWitness observedSurface state observerBudget haccepted).residualShadow ≤
      (thermodynamicBoundedWitness observedSurface state observerBudget haccepted).observerBudget :=
  runtime_bounded_witness_shadow_covered
    (thermodynamicBoundedWitness observedSurface state observerBudget haccepted)

def meshRoutingBoundedWitness
    (observedSurface : Nat)
    (state : MeshRoutingResidualState)
    (observerBudget : Nat)
    (haccepted : meshRoutingResidual state () ≤ observerBudget) :
    RuntimeBoundedWitnessCertificate :=
  meshRoutingBoundedWitnessAdapter.toWitness
    observedSurface state observerBudget haccepted

theorem mesh_routing_bounded_witness_shadow_covered
    (observedSurface : Nat)
    (state : MeshRoutingResidualState)
    (observerBudget : Nat)
    (haccepted : meshRoutingResidual state () ≤ observerBudget) :
    (meshRoutingBoundedWitness observedSurface state observerBudget haccepted).residualShadow ≤
      (meshRoutingBoundedWitness observedSurface state observerBudget haccepted).observerBudget :=
  runtime_bounded_witness_shadow_covered
    (meshRoutingBoundedWitness observedSurface state observerBudget haccepted)

def attentionBoundedWitness
    (observedSurface : Nat)
    (state : AttentionResidualState)
    (observerBudget : Nat)
    (haccepted : attentionResidual state () ≤ observerBudget) :
    RuntimeBoundedWitnessCertificate :=
  attentionBoundedWitnessAdapter.toWitness
    observedSurface state observerBudget haccepted

theorem attention_bounded_witness_shadow_covered
    (observedSurface : Nat)
    (state : AttentionResidualState)
    (observerBudget : Nat)
    (haccepted : attentionResidual state () ≤ observerBudget) :
    (attentionBoundedWitness observedSurface state observerBudget haccepted).residualShadow ≤
      (attentionBoundedWitness observedSurface state observerBudget haccepted).observerBudget :=
  runtime_bounded_witness_shadow_covered
    (attentionBoundedWitness observedSurface state observerBudget haccepted)

def finiteApproximationBoundedWitness
    (observedSurface : Nat)
    (state : FiniteApproximationResidualState)
    (observerBudget : Nat)
    (haccepted : finiteApproximationResidual state () ≤ observerBudget) :
    RuntimeBoundedWitnessCertificate :=
  finiteApproximationBoundedWitnessAdapter.toWitness
    observedSurface state observerBudget haccepted

theorem finite_approximation_bounded_witness_shadow_covered
    (observedSurface : Nat)
    (state : FiniteApproximationResidualState)
    (observerBudget : Nat)
    (haccepted : finiteApproximationResidual state () ≤ observerBudget) :
    (finiteApproximationBoundedWitness observedSurface state observerBudget haccepted).residualShadow ≤
      (finiteApproximationBoundedWitness observedSurface state observerBudget haccepted).observerBudget :=
  runtime_bounded_witness_shadow_covered
    (finiteApproximationBoundedWitness observedSurface state observerBudget haccepted)

/-! ## End-to-end bounded workflow example -/

def boundedWitnessWorkflowExamplePipeline :
    RuntimeBoundedWitnessPipeline :=
  let queue :=
    queueBoundedWitness 1
      { backlog := 7, serviceDebt := 3 } 33 (by native_decide)
  let thermo :=
    thermodynamicBoundedWitness 1
      { heatLeak := 2, entropyDebt := 4 } 33 (by native_decide)
  let mesh :=
    meshRoutingBoundedWitness 1
      { unroutedPressure := 5, capacityDebt := 1 } 33 (by native_decide)
  let attention :=
    attentionBoundedWitness 1
      { missedWeight := 3, saturationDebt := 2 } 33 (by native_decide)
  let approximation :=
    finiteApproximationBoundedWitness 1
      { discretizationError := 4, truncationError := 2 } 33 (by native_decide)
  { witnesses := [queue, thermo, mesh, attention, approximation]
    residualShadow := 33
    observerBudget := 33
    residualAccounts := by native_decide
    accepted := Nat.le_refl 33 }

theorem bounded_witness_workflow_example_process_chain_residual :
    boundedWitnessWorkflowExamplePipeline.toProcessChain.residual = 33 :=
  rfl

theorem bounded_witness_workflow_example_no_hidden_defect
    (wider : Nat)
    (observer : ScalarObserver)
    (depth : Nat)
    (hcovers : ObserverBudgetCovers natBudgetMeasure 33 wider)
    (hbudget : wider ≤ depth) :
    natResidualSignature.answer
      (probabilityObserverPromotion.promote
        boundedWitnessWorkflowExamplePipeline.toProcessChain.residualState ())
      observer depth :=
  runtime_bounded_witness_pipeline_process_chain_no_hidden_defect
    boundedWitnessWorkflowExamplePipeline wider observer depth hcovers hbudget

end FiniteProbabilityCore
end Gnosis
