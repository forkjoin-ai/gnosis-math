import Gnosis.Bridges.MediationQueueBoundaryBridge

/-!
# Mediation Geometric Witness Bridge

Positive mediation loss bundled with explicit kernel/envelope/rate witnesses.
-/

namespace MediationGeometricWitnessBridge

abbrev MediationSetup := Gnosis.CausalMediation.MediationSetup

structure CountableCertifiedKernel where
  atom : Nat
  maxQueue : Nat
  hAtomLeMax : atom ≤ maxQueue
deriving Repr

structure GeometricRateNat where
  numerator : Nat
  denominator : Nat
  initialBound : Nat
  hRateLtOne : numerator < denominator
  hDenomPos : 0 < denominator
  hInitialBoundPos : 0 < initialBound
deriving Repr

structure CountableQuantitativeGeometricEnvelopeAtAtom where
  atom : Nat
  rate : GeometricRateNat
  hAtomPositiveMass : 0 < rate.initialBound
deriving Repr

structure GeometricErgodicWitness where
  kernel : CountableCertifiedKernel
  envelope : CountableQuantitativeGeometricEnvelopeAtAtom
  rate : GeometricRateNat
  hKernelAtomMatchesEnvelope : kernel.atom = envelope.atom
  hEnvelopeRateMatches : envelope.rate = rate
deriving Repr

def mediationGeometricRate (m : MediationSetup) : GeometricRateNat :=
  { numerator := 3
    denominator := 4
    initialBound := m.mediatorLoss + 1
    hRateLtOne := by decide
    hDenomPos := by decide
    hInitialBoundPos := Nat.succ_pos m.mediatorLoss }

theorem mediation_loss_rate_consistency
    (m : MediationSetup) :
    (mediationGeometricRate m).numerator < (mediationGeometricRate m).denominator ∧
    0 < (mediationGeometricRate m).initialBound :=
  ⟨(mediationGeometricRate m).hRateLtOne,
    (mediationGeometricRate m).hInitialBoundPos⟩

theorem mediation_kernel_envelope_consistency
    (witness : GeometricErgodicWitness) :
    witness.kernel.atom = witness.envelope.atom ∧
    witness.envelope.rate = witness.rate :=
  ⟨witness.hKernelAtomMatchesEnvelope, witness.hEnvelopeRateMatches⟩

theorem mediation_loss_to_explicit_geometric_witness
    (m : MediationSetup)
    (witness : GeometricErgodicWitness)
    (hRate : witness.rate = mediationGeometricRate m) :
    1 ≤ m.mediatorLoss ∧
    witness.kernel.atom = witness.envelope.atom ∧
    witness.envelope.rate = witness.rate ∧
    witness.rate.numerator < witness.rate.denominator ∧
    0 < witness.rate.initialBound := by
  have hRateLt : witness.rate.numerator < witness.rate.denominator := by
    rw [hRate]
    exact (mediationGeometricRate m).hRateLtOne
  have hInitial : 0 < witness.rate.initialBound := by
    rw [hRate]
    exact (mediationGeometricRate m).hInitialBoundPos
  exact
    ⟨m.mediatorLossPositive,
      witness.hKernelAtomMatchesEnvelope,
      witness.hEnvelopeRateMatches,
      hRateLt,
      hInitial⟩

end MediationGeometricWitnessBridge
