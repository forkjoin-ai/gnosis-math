namespace KiCombatKnapsackQueueKernelBridge

/-! Init-only Ki + combat + knapsack queue bridge. -/

structure KiLeakSetup where
  totalLeak : Nat
  hLeak : 0 < totalLeak
deriving Repr

structure CombatSetup where
  entanglement : Nat
  hEntanglement : 0 < entanglement
deriving Repr

structure KnapsackSetup where
  screenCapacity : Nat
  visualOverlap : Nat
  pleromicData : Nat
  hOverlap : 1 ≤ visualOverlap
  hPleromic : pleromicData = screenCapacity + visualOverlap
deriving Repr

def kiCombatKnapsackFailureBudget
    (ki : KiLeakSetup) (combat : CombatSetup) (knapsack : KnapsackSetup) : Nat :=
  ki.totalLeak + combat.entanglement + knapsack.pleromicData

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
  { beta1 := 0, capacity := 1, arrivalRate := budget,
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
  { numerator := 3, denominator := 4, initialBound := budget + 1,
    hRateLtOne := by decide, hDenomPos := by decide,
    hInitialBoundPos := Nat.succ_pos budget }

theorem knapsack_pleromic_positive (knapsack : KnapsackSetup) :
    0 < knapsack.pleromicData := by
  rw [knapsack.hPleromic]
  exact Nat.lt_add_left knapsack.screenCapacity knapsack.hOverlap

theorem ki_combat_knapsack_budget_positive
    (ki : KiLeakSetup) (combat : CombatSetup) (knapsack : KnapsackSetup) :
    0 < kiCombatKnapsackFailureBudget ki combat knapsack := by
  unfold kiCombatKnapsackFailureBudget
  exact Nat.lt_add_right knapsack.pleromicData
    (Nat.lt_add_right combat.entanglement ki.hLeak)

theorem ki_combat_knapsack_budget_yields_unit_queue_boundary
    (ki : KiLeakSetup) (combat : CombatSetup) (knapsack : KnapsackSetup) :
    0 < ki.totalLeak ∧ 0 < combat.entanglement ∧
    knapsack.pleromicData = knapsack.screenCapacity + knapsack.visualOverlap ∧
    0 < knapsack.visualOverlap ∧
    ∃ boundary : QueueBoundaryWitnessNat,
      boundary.beta1 = 0 ∧ boundary.capacity = 1 ∧
      boundary.arrivalRate = kiCombatKnapsackFailureBudget ki combat knapsack ∧
      boundary.serviceRate =
        quorumSize (replicaCount (kiCombatKnapsackFailureBudget ki combat knapsack))
          (kiCombatKnapsackFailureBudget ki combat knapsack) := by
  exact ⟨ki.hLeak, combat.hEntanglement, knapsack.hPleromic, knapsack.hOverlap,
    ⟨canonicalQueueBoundary (kiCombatKnapsackFailureBudget ki combat knapsack),
      rfl, rfl, rfl, rfl⟩⟩

theorem ki_combat_knapsack_budget_yields_positive_topological_deficit
    (ki : KiLeakSetup) (combat : CombatSetup) (knapsack : KnapsackSetup) :
    0 < topologicalDeficit (kiCombatKnapsackFailureBudget ki combat knapsack + 1) 1 := by
  unfold topologicalDeficit
  rw [Nat.add_sub_cancel]
  exact ki_combat_knapsack_budget_positive ki combat knapsack

theorem ki_combat_knapsack_budget_does_not_force_beta1_equals_budget
    (ki : KiLeakSetup) (combat : CombatSetup) (knapsack : KnapsackSetup) :
    ¬ (∀ boundary : QueueBoundaryWitnessNat,
        boundary.arrivalRate = kiCombatKnapsackFailureBudget ki combat knapsack →
        boundary.serviceRate =
          quorumSize (replicaCount (kiCombatKnapsackFailureBudget ki combat knapsack))
            (kiCombatKnapsackFailureBudget ki combat knapsack) →
        boundary.beta1 = kiCombatKnapsackFailureBudget ki combat knapsack) := by
  intro hAll
  let boundary := canonicalQueueBoundary (kiCombatKnapsackFailureBudget ki combat knapsack)
  have hEq := hAll boundary rfl rfl
  have hZero : kiCombatKnapsackFailureBudget ki combat knapsack = 0 := Eq.symm hEq
  exact (Nat.ne_of_gt (ki_combat_knapsack_budget_positive ki combat knapsack)) hZero

theorem ki_combat_knapsack_budget_does_not_force_capacity_at_least_two
    (ki : KiLeakSetup) (combat : CombatSetup) (knapsack : KnapsackSetup) :
    ¬ (∀ boundary : QueueBoundaryWitnessNat,
        boundary.arrivalRate = kiCombatKnapsackFailureBudget ki combat knapsack →
        boundary.serviceRate =
          quorumSize (replicaCount (kiCombatKnapsackFailureBudget ki combat knapsack))
            (kiCombatKnapsackFailureBudget ki combat knapsack) →
        2 ≤ boundary.capacity) := by
  intro hAll
  let boundary := canonicalQueueBoundary (kiCombatKnapsackFailureBudget ki combat knapsack)
  exact Nat.not_succ_le_self 1 (hAll boundary rfl rfl)

theorem ki_combat_knapsack_semantic_morphism_yields_unit_queue_boundary
    (ki : KiLeakSetup) (combat : CombatSetup) (knapsack : KnapsackSetup)
    (interpret : Nat → Nat)
    (hInterpret :
      interpret (ki.totalLeak + combat.entanglement + knapsack.pleromicData) =
        kiCombatKnapsackFailureBudget ki combat knapsack) :
    0 < interpret (ki.totalLeak + combat.entanglement + knapsack.pleromicData) ∧
    ∃ boundary : QueueBoundaryWitnessNat,
      boundary.beta1 = 0 ∧ boundary.capacity = 1 ∧
      boundary.arrivalRate =
        interpret (ki.totalLeak + combat.entanglement + knapsack.pleromicData) ∧
      boundary.serviceRate =
        quorumSize
          (replicaCount (interpret (ki.totalLeak + combat.entanglement + knapsack.pleromicData)))
          (interpret (ki.totalLeak + combat.entanglement + knapsack.pleromicData)) := by
  rw [hInterpret]
  exact ⟨ki_combat_knapsack_budget_positive ki combat knapsack,
    ⟨canonicalQueueBoundary (kiCombatKnapsackFailureBudget ki combat knapsack),
      rfl, rfl, rfl, rfl⟩⟩

theorem ki_combat_knapsack_budget_yields_geometric_rate_certificate
    (ki : KiLeakSetup) (combat : CombatSetup) (knapsack : KnapsackSetup) :
    ∃ rate : GeometricRateNat,
      rate = budgetGeometricRate (kiCombatKnapsackFailureBudget ki combat knapsack) ∧
      rate.initialBound = kiCombatKnapsackFailureBudget ki combat knapsack + 1 ∧
      rate.numerator = 3 ∧ rate.denominator = 4 ∧
      rate.numerator < rate.denominator ∧ 0 < rate.initialBound := by
  refine ⟨budgetGeometricRate (kiCombatKnapsackFailureBudget ki combat knapsack),
    rfl, rfl, rfl, rfl, ?_, ?_⟩
  · exact (budgetGeometricRate (kiCombatKnapsackFailureBudget ki combat knapsack)).hRateLtOne
  · exact (budgetGeometricRate (kiCombatKnapsackFailureBudget ki combat knapsack)).hInitialBoundPos

structure CompiledWitnessNat where
  budget : Nat
  atomMass : Nat
  minorizationMass : Nat
  driftGap : Nat
  hBudget : 0 < budget
  hAtom : 0 < atomMass
  hMinorization : 0 < minorizationMass
  hDriftGap : 0 < driftGap
deriving Repr

def kiCombatKnapsackCompileWitnessFromPrimitives
    (ki : KiLeakSetup) (combat : CombatSetup) (knapsack : KnapsackSetup)
    (atomMass minorizationMass driftGap : Nat)
    (hAtom : 0 < atomMass)
    (hMinorization : 0 < minorizationMass)
    (hDriftGap : 0 < driftGap) : CompiledWitnessNat :=
  { budget := kiCombatKnapsackFailureBudget ki combat knapsack
    atomMass := atomMass
    minorizationMass := minorizationMass
    driftGap := driftGap
    hBudget := ki_combat_knapsack_budget_positive ki combat knapsack
    hAtom := hAtom
    hMinorization := hMinorization
    hDriftGap := hDriftGap }

theorem ki_combat_knapsack_compile_witness_from_primitives
    (ki : KiLeakSetup) (combat : CombatSetup) (knapsack : KnapsackSetup)
    (atomMass minorizationMass driftGap : Nat)
    (hAtom : 0 < atomMass)
    (hMinorization : 0 < minorizationMass)
    (hDriftGap : 0 < driftGap) :
    ∃ witness : CompiledWitnessNat,
      witness.budget = kiCombatKnapsackFailureBudget ki combat knapsack ∧
      0 < witness.atomMass ∧ 0 < witness.minorizationMass ∧ 0 < witness.driftGap := by
  exact ⟨kiCombatKnapsackCompileWitnessFromPrimitives
      ki combat knapsack atomMass minorizationMass driftGap hAtom hMinorization hDriftGap,
    rfl, hAtom, hMinorization, hDriftGap⟩

theorem ki_combat_knapsack_compiled_witness_continuous_ergodicity_lift
    (ki : KiLeakSetup) (combat : CombatSetup) (knapsack : KnapsackSetup)
    (atomMass minorizationMass driftGap : Nat)
    (hAtom : 0 < atomMass)
    (hMinorization : 0 < minorizationMass)
    (hDriftGap : 0 < driftGap) :
    ∃ witness : CompiledWitnessNat,
      0 < witness.budget ∧ 0 < witness.driftGap := by
  let witness :=
    kiCombatKnapsackCompileWitnessFromPrimitives
      ki combat knapsack atomMass minorizationMass driftGap hAtom hMinorization hDriftGap
  exact ⟨witness, witness.hBudget, witness.hDriftGap⟩

end KiCombatKnapsackQueueKernelBridge
