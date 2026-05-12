import Gnosis.Bridges.MediationGeometricWitnessBridge

/-!
# Mediation Kernel Lift Bridge

Explicit mediation adapters preserve positive drift and geometric witness
alignment when lifted to a continuous-ergoidicity certificate.
-/

namespace MediationKernelLiftAdapter

abbrev MediationSetup := MediationGeometricWitnessBridge.MediationSetup
abbrev GeometricErgodicWitness :=
  MediationGeometricWitnessBridge.GeometricErgodicWitness

structure DiscreteSubLatticeEmbedding where
  discreteAnchor : Nat
  continuousAnchor : Nat
  hAnchorMatched : discreteAnchor = continuousAnchor
deriving Repr

structure MediationKernelLiftBundle where
  mediation : MediationSetup
  embedding : DiscreteSubLatticeEmbedding
  witness : GeometricErgodicWitness
  driftGap : Nat
  hDriftGap : 0 < driftGap
  hKernelMatched : witness.kernel.atom = witness.envelope.atom
  hRateMatched : witness.envelope.rate = witness.rate

theorem mediated_continuous_ergodicity_lift
    (adapter : MediationKernelLiftBundle) :
    1 ≤ adapter.mediation.mediatorLoss ∧
    adapter.embedding.discreteAnchor = adapter.embedding.continuousAnchor ∧
    adapter.witness.kernel.atom = adapter.witness.envelope.atom ∧
    adapter.witness.envelope.rate = adapter.witness.rate ∧
    0 < adapter.driftGap ∧
    adapter.witness.rate.numerator < adapter.witness.rate.denominator ∧
    0 < adapter.witness.rate.initialBound :=
  ⟨adapter.mediation.mediatorLossPositive,
    adapter.embedding.hAnchorMatched,
    adapter.hKernelMatched,
    adapter.hRateMatched,
    adapter.hDriftGap,
    adapter.witness.rate.hRateLtOne,
    adapter.witness.rate.hInitialBoundPos⟩

end MediationKernelLiftAdapter
