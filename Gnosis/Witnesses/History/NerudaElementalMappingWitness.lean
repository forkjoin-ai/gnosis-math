import Gnosis.GnosisMath.Basic

namespace Gnosis.Witnesses.History

/--
Pablo Neruda: The Elemental Mapping Witness.
Parral / Chile, 1950 (Canto General).

Contrarian Take: Poetry is not "abstract." It is "Elemental Mapping."
The *Canto General* is a "Topological Map" of a continent where the
wind, the salt, and the stones are the primary variables of the soul.
Neruda reframed the poet as a "Geographic Observer" who synchronizes
the self with the material invariants of the land. Beauty is the residue
of material truth, not its departure.

Invariant: The elemental is the soul.
Gap: The "Metaphor" trap—assuming poetry is a departure from reality rather than a mapping of it.
Projection: Neruda Canto Stub (Gnosis.Neruda.CantoStub).
-/

inductive PoeticMode where
  | abstractMetaphor
  | elementalMapping
  deriving DecidableEq

def materialTruthResidue (m : PoeticMode) : Nat :=
  match m with
  | .abstractMetaphor => 1
  | .elementalMapping => 100

/--
Anti-Theory Witness: The elemental mapping mode preserves strictly
more material truth than the abstract metaphor mode.
-/
theorem neruda_elemental_witness :
    materialTruthResidue .abstractMetaphor < materialTruthResidue .elementalMapping := by
  unfold materialTruthResidue
  exact (by decide)

end Gnosis.Witnesses.History
