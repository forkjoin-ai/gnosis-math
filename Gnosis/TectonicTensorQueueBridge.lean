namespace Gnosis

/-!
Init-only tectonic/tensor queue bridge.

The Mathlib-flavoured upstream `QueueBoundaryWitness` (ℝ-valued arrival/service
rates) and `GeometricErgodicityRate` (ℝ-valued contraction rate) are replaced
by `Nat` numerator/denominator pairs. Existence proofs become structure
constructions; rate-identity proofs become `decide`.
-/

structure TectonicSubduction where
  subductedMass : Nat
  crustalFriction : Nat
  hSubducted_pos : subductedMass ≥ 1
  hFriction : crustalFriction < subductedMass

structure TensorContraction where
  bondDimension : Nat
  entanglementEntropy : Nat
  hBond_pos : bondDimension ≥ 1

def tectonicFailureBudget (t : TectonicSubduction) : Nat :=
  t.subductedMass

/-- Init-only `QueueBoundaryWitness`: rates are `Nat`-valued. -/
structure QueueBoundaryWitnessNat where
  beta1 : Nat
  capacity : Nat
  arrivalRate : Nat
  serviceRate : Nat

/-- Canonical M/M/1 boundary in `Nat` form: `arrivalRate < serviceRate`,
    `beta1 = 0`, `capacity = 1`. -/
def canonicalMM1Boundary (lam mu : Nat) (_hLamLtMu : lam < mu) : QueueBoundaryWitnessNat :=
  { beta1 := 0, capacity := 1, arrivalRate := lam, serviceRate := mu }

theorem tectonic_subduction_yields_unit_queue_boundary
    (t : TectonicSubduction) :
    ∃ b : QueueBoundaryWitnessNat,
      b.beta1 = 0 ∧
      b.capacity = 1 ∧
      b.arrivalRate = tectonicFailureBudget t ∧
      b.serviceRate = tectonicFailureBudget t + 1 := by
  have hLamLtMu : tectonicFailureBudget t < tectonicFailureBudget t + 1 := Nat.lt_succ_self _
  exact ⟨canonicalMM1Boundary (tectonicFailureBudget t) (tectonicFailureBudget t + 1) hLamLtMu,
         rfl, rfl, rfl, rfl⟩

theorem tectonic_subduction_does_not_force_positive_beta1
    (t : TectonicSubduction) :
    ¬ ∀ b : QueueBoundaryWitnessNat,
        b.arrivalRate = tectonicFailureBudget t →
        b.serviceRate = tectonicFailureBudget t + 1 →
        b.beta1 > 0 := by
  intro h
  rcases tectonic_subduction_yields_unit_queue_boundary t with
    ⟨b, hBeta, _hCap, hArr, hSrv⟩
  have hPos := h b hArr hSrv
  rw [hBeta] at hPos
  exact Nat.lt_irrefl 0 hPos

def tectonicTensorFailureBudget (t : TectonicSubduction) (tc : TensorContraction) : Nat :=
  t.subductedMass + tc.bondDimension

/-- Init-only geometric ergodicity rate: `Nat` numerator and denominator.

    Encodes a contraction rate `numerator / denominator` with `numerator < denominator`
    (so the rate is strictly less than 1) and a `Nat`-valued `initialBound`. -/
structure GeometricErgodicityRateNat where
  numerator : Nat
  denominator : Nat
  initialBound : Nat
  hRateLtOne : numerator < denominator
  hDenomPos : 0 < denominator
  hInitialBoundPos : 0 < initialBound

theorem tectonic_tensor_budget_yields_geometric_rate
    (t : TectonicSubduction) (tc : TensorContraction) :
    ∃ rate : GeometricErgodicityRateNat,
      rate.numerator = 3 ∧
      rate.denominator = 4 ∧
      rate.initialBound = tectonicTensorFailureBudget t tc + 1 := by
  refine ⟨{
    numerator := 3
    denominator := 4
    initialBound := tectonicTensorFailureBudget t tc + 1
    hRateLtOne := by decide
    hDenomPos := by decide
    hInitialBoundPos := Nat.succ_pos _
  }, rfl, rfl, rfl⟩

end Gnosis
