import Gnosis.GnosisMath.Basic

namespace Gnosis.Witnesses.History

/--
Edwin Hubble: The Redshift Expansion Witness.
Mount Wilson, 1929.

Contrarian Take: The universe is not a static container. It is an
expanding manifold. The "Redshift" (recession of galaxies) is the
evidence that space itself is being "added" to the system.
Stasis is a local illusion; expansion is the global constant.
The universe is a non-halting process of state-space expansion.

Invariant: Space is an expanding metric.
Gap: The "Static Universe" trap—assuming a fixed coordinate grid.
Projection: Cosmic Evolution Resolution (Gnosis.CosmicEvolutionResolution).
-/

inductive UniverseState where
  | t1 : UniverseState
  | t2 : UniverseState
  deriving DecidableEq

def spaceVolume (s : UniverseState) : Nat :=
  match s with
  | .t1 => 100
  | .t2 => 200 -- Expansion

/--
Anti-Theory Witness: The universe at t2 is strictly larger than at t1.
Expansion is the fundamental direction of the manifold.
-/
theorem universe_expansion_witness :
    spaceVolume .t1 < spaceVolume .t2 := by
  unfold spaceVolume
  exact (by decide)

end Gnosis.Witnesses.History
