import Gnosis.GnosisMath.Basic

namespace Gnosis.Witnesses.History

/--
Niels Bohr: The Complementarity Witness.
Copenhagen, 1927.

Contrarian Take: Wave-Particle duality is not a "mystery" or a "paradox."
It is a "Mutually Exclusive Constraint." You can measure position (particle)
or momentum (wave), but not both simultaneously because the act of
measurement is a dimensional collapse. The "Quantum World" is a
high-dimensional object that we can only view through low-dimensional
projections. Complementarity is the recognition that the "Full State"
cannot be contained in a single observer-frame.

Invariant: Information is preserved, but visibility is constrained.
Gap: The "Exhaustive Observation" trap—assuming we can see the whole state at once.
Projection: Amplituhedron Antisymmetry No-Go (Gnosis.AmplituhedronAntisymmetryNoGo).
-/

inductive ObservationFrame where
  | waveFrame     : ObservationFrame
  | particleFrame : ObservationFrame
  deriving DecidableEq

def observableFeature (f : ObservationFrame) : String :=
  match f with
  | .waveFrame     => "momentum"
  | .particleFrame => "position"

/--
Anti-Theory Witness: No single frame can observe both momentum and position.
Knowledge is partitioned by the observer's frame.
-/
theorem bohr_complementarity_witness :
    observableFeature .waveFrame ≠ observableFeature .particleFrame := by
  unfold observableFeature
  exact (by decide)

end Gnosis.Witnesses.History
