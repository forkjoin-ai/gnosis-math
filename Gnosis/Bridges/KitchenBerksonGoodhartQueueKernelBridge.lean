import Init
import Gnosis.BerksonsParadox
import Gnosis.Bridges.BerksonQueueKernelBridge
import Gnosis.Bridges.KitchenBerksonQueueKernelBridge

/-!
# Kitchen/Berkson/Goodhart Queue Kernel Bridge

Finite tri-domain queue witnesses for kitchen coordination deficit, selected
Berkson collider threshold, and Goodhart proxy-gap accounting.
-/

namespace KitchenBerksonGoodhartQueueKernelBridge

abbrev CrossDomainFrame := KitchenBerksonQueueKernelBridge.CrossDomainFrame

structure GoodhartSetup where
  vTrue : Nat
  vGamed : Nat
  hGamedLeTrue : vGamed ≤ vTrue
deriving Repr

def goodhartProxyGap (goodhart : GoodhartSetup) : Nat :=
  goodhart.vTrue - goodhart.vGamed

def triDomainBudget
    (frame : CrossDomainFrame)
    (collider : BerksonsParadox.ColliderSetup)
    (goodhart : GoodhartSetup) : Nat :=
  KitchenBerksonQueueKernelBridge.totalDeficit frame
    + BerksonQueueKernelBridge.colliderThreshold collider
    + goodhartProxyGap goodhart

def topologicalDeficit (pathCount channelCount : Nat) : Nat :=
  pathCount - channelCount

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

theorem tri_domain_budget_positive
    (frame : CrossDomainFrame)
    (collider : BerksonsParadox.ColliderSetup)
    (goodhart : GoodhartSetup)
    (hGap : frame.safetySignals < frame.safetyHazards) :
    0 < triDomainBudget frame collider goodhart := by
  unfold triDomainBudget
  rw [Nat.add_assoc]
  exact Nat.lt_add_right
    (BerksonQueueKernelBridge.colliderThreshold collider + goodhartProxyGap goodhart)
    (KitchenBerksonQueueKernelBridge.safety_gap_positive frame hGap)

theorem kitchen_berkson_goodhart_budget_yields_unit_queue_boundary
    (frame : CrossDomainFrame)
    (collider : BerksonsParadox.ColliderSetup)
    (goodhart : GoodhartSetup)
    (hCritical : frame.physicalSafetyCritical = true)
    (hGap : frame.safetySignals < frame.safetyHazards)
    (hSelected : collider.selected) :
    frame.physicalSafetyCritical = true ∧
    0 < KitchenBerksonQueueKernelBridge.totalDeficit frame ∧
    BerksonQueueKernelBridge.colliderThreshold collider ≤
      BerksonQueueKernelBridge.totalRejections collider ∧
    goodhartProxyGap goodhart = goodhart.vTrue - goodhart.vGamed ∧
    ∃ boundary : QueueBoundaryWitnessNat,
      boundary.beta1 = 0 ∧
      boundary.capacity = 1 ∧
      boundary.arrivalRate = triDomainBudget frame collider goodhart ∧
      boundary.serviceRate =
        quorumSize
          (replicaCount (triDomainBudget frame collider goodhart))
          (triDomainBudget frame collider goodhart) := by
  exact ⟨hCritical,
    KitchenBerksonQueueKernelBridge.safety_gap_positive frame hGap,
    BerksonQueueKernelBridge.berkson_selected_implies_threshold_bounded_by_total_rejections
      collider
      hSelected,
    rfl,
    ⟨canonicalQueueBoundary (triDomainBudget frame collider goodhart),
      rfl, rfl, rfl, rfl⟩⟩

theorem kitchen_berkson_goodhart_budget_yields_positive_topological_deficit
    (frame : CrossDomainFrame)
    (collider : BerksonsParadox.ColliderSetup)
    (goodhart : GoodhartSetup)
    (hGap : frame.safetySignals < frame.safetyHazards) :
    0 < triDomainBudget frame collider goodhart ∧
    0 < topologicalDeficit (triDomainBudget frame collider goodhart + 1) 1 := by
  have hBudget : 0 < triDomainBudget frame collider goodhart :=
    tri_domain_budget_positive frame collider goodhart hGap
  refine ⟨hBudget, ?_⟩
  unfold topologicalDeficit
  rw [Nat.add_sub_cancel]
  exact hBudget

theorem kitchen_berkson_goodhart_budget_does_not_force_beta1_equals_budget
    (frame : CrossDomainFrame)
    (collider : BerksonsParadox.ColliderSetup)
    (goodhart : GoodhartSetup)
    (hGap : frame.safetySignals < frame.safetyHazards) :
    ¬ (∀ boundary : QueueBoundaryWitnessNat,
        boundary.arrivalRate = triDomainBudget frame collider goodhart →
        boundary.serviceRate =
          quorumSize
            (replicaCount (triDomainBudget frame collider goodhart))
            (triDomainBudget frame collider goodhart) →
        boundary.beta1 = triDomainBudget frame collider goodhart) := by
  intro hAll
  let boundary := canonicalQueueBoundary (triDomainBudget frame collider goodhart)
  have hEq : boundary.beta1 = triDomainBudget frame collider goodhart :=
    hAll boundary rfl rfl
  have hPositive : 0 < triDomainBudget frame collider goodhart :=
    tri_domain_budget_positive frame collider goodhart hGap
  rw [show boundary.beta1 = 0 by rfl] at hEq
  rw [← hEq] at hPositive
  exact Nat.lt_irrefl 0 hPositive

structure PrimitiveKernelObligations where
  atomInSmallSet : Bool
  epsilonOne : Nat
  epsilonTwo : Nat
  hEpsilonOnePos : 0 < epsilonOne
  hEpsilonTwoPos : 0 < epsilonTwo
  kernelAligned : Bool
deriving Repr

structure CompiledGoodhartWitness where
  budget : Nat
  rate : GeometricRateNat
  primitives : PrimitiveKernelObligations
deriving Repr

def compiledWitness
    (frame : CrossDomainFrame)
    (collider : BerksonsParadox.ColliderSetup)
    (goodhart : GoodhartSetup)
    (primitives : PrimitiveKernelObligations) : CompiledGoodhartWitness :=
  { budget := triDomainBudget frame collider goodhart
    rate := budgetGeometricRate (triDomainBudget frame collider goodhart)
    primitives := primitives }

theorem kitchen_berkson_goodhart_compile_witness_from_primitives
    (frame : CrossDomainFrame)
    (collider : BerksonsParadox.ColliderSetup)
    (goodhart : GoodhartSetup)
    (primitives : PrimitiveKernelObligations) :
    ∃ witness : CompiledGoodhartWitness,
      witness = compiledWitness frame collider goodhart primitives ∧
      witness.budget = triDomainBudget frame collider goodhart ∧
      witness.rate.initialBound = triDomainBudget frame collider goodhart + 1 ∧
      witness.rate.numerator = 3 ∧
      witness.rate.denominator = 4 ∧
      witness.rate.numerator < witness.rate.denominator ∧
      0 < witness.rate.initialBound ∧
      0 < witness.primitives.epsilonOne ∧
      0 < witness.primitives.epsilonTwo := by
  refine ⟨compiledWitness frame collider goodhart primitives,
    rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · exact (budgetGeometricRate (triDomainBudget frame collider goodhart)).hRateLtOne
  · exact (budgetGeometricRate (triDomainBudget frame collider goodhart)).hInitialBoundPos
  · exact primitives.hEpsilonOnePos
  · exact primitives.hEpsilonTwoPos

structure KitchenBerksonGoodhartKernelLiftBundle where
  frame : CrossDomainFrame
  collider : BerksonsParadox.ColliderSetup
  goodhart : GoodhartSetup
  primitives : PrimitiveKernelObligations
  hCritical : frame.physicalSafetyCritical = true
  hGap : frame.safetySignals < frame.safetyHazards
  hSelected : collider.selected
  budget : Nat
  hBudgetEq : budget = triDomainBudget frame collider goodhart
  driftGap : Nat
  hDriftGap : 0 < driftGap

theorem kitchen_berkson_goodhart_compiled_witness_continuous_ergodicity_lift
    (adapter : KitchenBerksonGoodhartKernelLiftBundle) :
    adapter.frame.physicalSafetyCritical = true ∧
    adapter.frame.safetySignals < adapter.frame.safetyHazards ∧
    BerksonQueueKernelBridge.colliderThreshold adapter.collider ≤
      BerksonQueueKernelBridge.totalRejections adapter.collider ∧
    adapter.budget =
      triDomainBudget adapter.frame adapter.collider adapter.goodhart ∧
    0 < adapter.budget ∧
    0 < adapter.driftGap ∧
    ∃ witness : CompiledGoodhartWitness,
      witness = compiledWitness adapter.frame adapter.collider adapter.goodhart adapter.primitives ∧
      witness.budget = adapter.budget := by
  refine ⟨adapter.hCritical, adapter.hGap, ?_, adapter.hBudgetEq, ?_, adapter.hDriftGap, ?_⟩
  · exact BerksonQueueKernelBridge.berkson_selected_implies_threshold_bounded_by_total_rejections
      adapter.collider
      adapter.hSelected
  · rw [adapter.hBudgetEq]
    exact tri_domain_budget_positive adapter.frame adapter.collider adapter.goodhart adapter.hGap
  · refine ⟨compiledWitness adapter.frame adapter.collider adapter.goodhart adapter.primitives, rfl, ?_⟩
    exact adapter.hBudgetEq.symm

end KitchenBerksonGoodhartQueueKernelBridge
