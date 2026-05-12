import Init

/-!
# Macro/Ecosystem/Tribology/Conversion Queue Kernel Bridge

Finite phantom-injection, keystone, slam-penalty, and conversion-vent witnesses
for stale MCP rows.
-/

namespace MacroEcosystemTribologyConversionQueueKernelBridge

structure MacroSetup where
  baseAssets : Nat
  fiatCrossings : Nat
  totalMarket : Nat
  hTotalMarket : totalMarket = baseAssets + fiatCrossings
  hFiat : 1 ≤ fiatCrossings
deriving Repr

structure EcosystemSetup where
  keystoneNode : Nat
  remaining : Nat
  ecosystemComplexity : Nat
  hComplexity : ecosystemComplexity = keystoneNode + remaining
  hKeystone : 1 ≤ keystoneNode
deriving Repr

structure TribologySetup where
  rawFriction : Nat
  lubricatedFriction : Nat
  slamPenalty : Nat
  hLubricated : lubricatedFriction < rawFriction
  hSlam : 1 ≤ slamPenalty
deriving Repr

structure ConversionSetup where
  uiFriction : Nat
  buleInvestment : Nat
  ventSlam : Nat
  hAbandon : buleInvestment < uiFriction
  hVent : ventSlam = uiFriction - buleInvestment
deriving Repr

def conversionVentFailureBudget (conversion : ConversionSetup) : Nat :=
  conversion.ventSlam

def macroEcosystemTribologyConversionFailureBudget
    (market : MacroSetup)
    (ecosystem : EcosystemSetup)
    (tribology : TribologySetup)
    (conversion : ConversionSetup) : Nat :=
  market.fiatCrossings + ecosystem.keystoneNode +
    conversionVentFailureBudget conversion + tribology.slamPenalty

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

theorem conversion_vent_positive (conversion : ConversionSetup) :
    0 < conversionVentFailureBudget conversion := by
  unfold conversionVentFailureBudget
  rw [conversion.hVent]
  exact Nat.sub_pos_of_lt conversion.hAbandon

theorem macro_ecosystem_tribology_conversion_budget_positive
    (market : MacroSetup)
    (ecosystem : EcosystemSetup)
    (tribology : TribologySetup)
    (conversion : ConversionSetup) :
    0 <
      macroEcosystemTribologyConversionFailureBudget
        market ecosystem tribology conversion := by
  unfold macroEcosystemTribologyConversionFailureBudget
  rw [Nat.add_assoc, Nat.add_assoc]
  exact Nat.lt_add_right
    (ecosystem.keystoneNode +
      (conversionVentFailureBudget conversion + tribology.slamPenalty))
    market.hFiat

theorem macro_ecosystem_tribology_conversion_budget_yields_unit_queue_boundary
    (market : MacroSetup)
    (ecosystem : EcosystemSetup)
    (tribology : TribologySetup)
    (conversion : ConversionSetup) :
    market.totalMarket = market.baseAssets + market.fiatCrossings ∧
    0 < market.fiatCrossings ∧
    ecosystem.ecosystemComplexity = ecosystem.keystoneNode + ecosystem.remaining ∧
    0 < ecosystem.keystoneNode ∧
    tribology.lubricatedFriction < tribology.rawFriction ∧
    0 < tribology.slamPenalty ∧
    conversion.ventSlam = conversion.uiFriction - conversion.buleInvestment ∧
    0 < conversionVentFailureBudget conversion ∧
    0 <
      macroEcosystemTribologyConversionFailureBudget
        market ecosystem tribology conversion ∧
    ∃ boundary : QueueBoundaryWitnessNat,
      boundary.beta1 = 0 ∧
      boundary.capacity = 1 ∧
      boundary.arrivalRate =
        macroEcosystemTribologyConversionFailureBudget
          market ecosystem tribology conversion ∧
      boundary.serviceRate =
        quorumSize
          (replicaCount
            (macroEcosystemTribologyConversionFailureBudget
              market ecosystem tribology conversion))
          (macroEcosystemTribologyConversionFailureBudget
            market ecosystem tribology conversion) := by
  exact ⟨market.hTotalMarket, market.hFiat, ecosystem.hComplexity,
    ecosystem.hKeystone, tribology.hLubricated, tribology.hSlam,
    conversion.hVent, conversion_vent_positive conversion,
    macro_ecosystem_tribology_conversion_budget_positive
      market ecosystem tribology conversion,
    ⟨canonicalQueueBoundary
      (macroEcosystemTribologyConversionFailureBudget
        market ecosystem tribology conversion),
      rfl, rfl, rfl, rfl⟩⟩

theorem macro_ecosystem_tribology_conversion_budget_yields_positive_topological_deficit
    (market : MacroSetup)
    (ecosystem : EcosystemSetup)
    (tribology : TribologySetup)
    (conversion : ConversionSetup) :
    0 < topologicalDeficit
      (macroEcosystemTribologyConversionFailureBudget
        market ecosystem tribology conversion + 1)
      1 := by
  unfold topologicalDeficit
  rw [Nat.add_sub_cancel]
  exact macro_ecosystem_tribology_conversion_budget_positive
    market ecosystem tribology conversion

theorem macro_ecosystem_tribology_conversion_budget_does_not_force_beta1_equals_budget
    (market : MacroSetup)
    (ecosystem : EcosystemSetup)
    (tribology : TribologySetup)
    (conversion : ConversionSetup) :
    ¬ (∀ boundary : QueueBoundaryWitnessNat,
        boundary.arrivalRate =
          macroEcosystemTribologyConversionFailureBudget
            market ecosystem tribology conversion →
        boundary.serviceRate =
          quorumSize
            (replicaCount
              (macroEcosystemTribologyConversionFailureBudget
                market ecosystem tribology conversion))
            (macroEcosystemTribologyConversionFailureBudget
              market ecosystem tribology conversion) →
        boundary.beta1 =
          macroEcosystemTribologyConversionFailureBudget
            market ecosystem tribology conversion) := by
  intro hAll
  let budget :=
    macroEcosystemTribologyConversionFailureBudget
      market ecosystem tribology conversion
  let boundary := canonicalQueueBoundary budget
  have hEq : boundary.beta1 = budget := hAll boundary rfl rfl
  have hPositive : 0 < budget :=
    macro_ecosystem_tribology_conversion_budget_positive
      market ecosystem tribology conversion
  rw [show boundary.beta1 = 0 by rfl] at hEq
  rw [← hEq] at hPositive
  exact Nat.lt_irrefl 0 hPositive

theorem macro_ecosystem_tribology_conversion_budget_does_not_force_capacity_at_least_two
    (market : MacroSetup)
    (ecosystem : EcosystemSetup)
    (tribology : TribologySetup)
    (conversion : ConversionSetup) :
    ¬ (∀ boundary : QueueBoundaryWitnessNat,
        boundary.arrivalRate =
          macroEcosystemTribologyConversionFailureBudget
            market ecosystem tribology conversion →
        boundary.serviceRate =
          quorumSize
            (replicaCount
              (macroEcosystemTribologyConversionFailureBudget
                market ecosystem tribology conversion))
            (macroEcosystemTribologyConversionFailureBudget
              market ecosystem tribology conversion) →
        2 ≤ boundary.capacity) := by
  intro hAll
  let budget :=
    macroEcosystemTribologyConversionFailureBudget
      market ecosystem tribology conversion
  let boundary := canonicalQueueBoundary budget
  have hCapacity : 2 ≤ 1 := hAll boundary rfl rfl
  exact (Nat.not_succ_le_self 1) hCapacity

theorem macro_ecosystem_tribology_conversion_semantic_morphism_yields_positive_topological_deficit
    (market : MacroSetup)
    (ecosystem : EcosystemSetup)
    (tribology : TribologySetup)
    (conversion : ConversionSetup)
    (interpret : Nat → Nat)
    (hInterpret :
      interpret
        (macroEcosystemTribologyConversionFailureBudget
          market ecosystem tribology conversion + 1) =
        macroEcosystemTribologyConversionFailureBudget
          market ecosystem tribology conversion + 1) :
    0 < topologicalDeficit
      (interpret
        (macroEcosystemTribologyConversionFailureBudget
          market ecosystem tribology conversion + 1))
      1 := by
  rw [hInterpret]
  exact
    macro_ecosystem_tribology_conversion_budget_yields_positive_topological_deficit
      market ecosystem tribology conversion

end MacroEcosystemTribologyConversionQueueKernelBridge
