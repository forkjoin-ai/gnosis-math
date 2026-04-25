namespace BuleyeanMath

/-!
Init-only mediation queue boundary bridge.

`mediatorLoss` is a positive `Nat`; rates are `Nat`-valued; the geometric
contraction rate is encoded as the pair `(numerator, denominator) = (3, 4)`.
-/

namespace CausalMediation

structure MediationSetup where
  mediatorLoss : Nat
  mediatorLossPositive : 1 ≤ mediatorLoss

end CausalMediation

structure QueueBoundaryWitnessNat where
  beta1 : Nat
  capacity : Nat
  arrivalRate : Nat
  serviceRate : Nat

def canonicalMM1Boundary (lam mu : Nat) (_h : lam < mu) : QueueBoundaryWitnessNat :=
  { beta1 := 0, capacity := 1, arrivalRate := lam, serviceRate := mu }

structure GeometricErgodicityRateNat where
  numerator : Nat
  denominator : Nat
  initialBound : Nat
  hRateLtOne : numerator < denominator
  hDenomPos : 0 < denominator
  hInitialBoundPos : 0 < initialBound

structure MultiLevelHarrisWitnessNat where
  levels : Nat
  discreteDriftGap : Nat
  continuousDriftGap : Nat
  hDiscrete : 0 < discreteDriftGap
  hContinuous : 0 < continuousDriftGap

theorem mediation_positive_loss_yields_unit_queue_boundary
    (m : CausalMediation.MediationSetup) :
    ∃ boundary : QueueBoundaryWitnessNat,
      boundary.beta1 = 0 ∧
      boundary.capacity = 1 ∧
      boundary.arrivalRate = m.mediatorLoss ∧
      boundary.serviceRate = m.mediatorLoss + 1 := by
  have h : m.mediatorLoss < m.mediatorLoss + 1 := Nat.lt_succ_self _
  exact ⟨canonicalMM1Boundary m.mediatorLoss (m.mediatorLoss + 1) h, rfl, rfl, rfl, rfl⟩

theorem mediation_loss_does_not_force_positive_beta1
    (m : CausalMediation.MediationSetup) :
    ¬ (∀ boundary : QueueBoundaryWitnessNat,
        boundary.arrivalRate = m.mediatorLoss →
        boundary.serviceRate = m.mediatorLoss + 1 →
        0 < boundary.beta1) := by
  intro hPositive
  rcases mediation_positive_loss_yields_unit_queue_boundary m with
    ⟨boundary, hBetaZero, _hCapacity, hArrival, hService⟩
  have hPos : 0 < boundary.beta1 := hPositive boundary hArrival hService
  rw [hBetaZero] at hPos
  exact Nat.lt_irrefl 0 hPos

def mediationLossGeometricRate (m : CausalMediation.MediationSetup) :
    GeometricErgodicityRateNat :=
  { numerator := 3
    denominator := 4
    initialBound := m.mediatorLoss + 1
    hRateLtOne := by decide
    hDenomPos := by decide
    hInitialBoundPos := Nat.succ_pos _ }

theorem mediation_positive_loss_yields_geometric_rate_certificate
    (m : CausalMediation.MediationSetup) :
    ∃ rate : GeometricErgodicityRateNat,
      rate = mediationLossGeometricRate m ∧
      rate.initialBound = m.mediatorLoss + 1 ∧
      rate.numerator = 3 ∧
      rate.denominator = 4 ∧
      rate.numerator < rate.denominator ∧
      1 < rate.initialBound := by
  refine ⟨mediationLossGeometricRate m, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · exact (mediationLossGeometricRate m).hRateLtOne
  · show 1 < m.mediatorLoss + 1
    exact Nat.succ_lt_succ (Nat.lt_of_lt_of_le Nat.zero_lt_one m.mediatorLossPositive)

def mediationLossMultiLevelWitness (m : CausalMediation.MediationSetup) :
    MultiLevelHarrisWitnessNat :=
  { levels := 2
    discreteDriftGap := m.mediatorLoss
    continuousDriftGap := m.mediatorLoss
    hDiscrete := Nat.lt_of_lt_of_le Nat.zero_lt_one m.mediatorLossPositive
    hContinuous := Nat.lt_of_lt_of_le Nat.zero_lt_one m.mediatorLossPositive }

theorem mediation_positive_loss_yields_multilevel_harris_witness
    (m : CausalMediation.MediationSetup) :
    ∃ witness : MultiLevelHarrisWitnessNat,
      witness = mediationLossMultiLevelWitness m ∧
      0 < witness.discreteDriftGap ∧
      0 < witness.continuousDriftGap := by
  refine ⟨mediationLossMultiLevelWitness m, rfl, ?_, ?_⟩
  · exact (mediationLossMultiLevelWitness m).hDiscrete
  · exact (mediationLossMultiLevelWitness m).hContinuous

end BuleyeanMath
