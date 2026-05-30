import Gnosis.GnosisMath.Basic

namespace Gnosis.Witnesses.History

/--
Charles Sanders Peirce: The Semiotic Triad Witness.
Cambridge, USA, 1860s-1900s.

Contrarian Take: Meaning is not a dualistic mapping (Sign -> Object).
It is a "Triadic Invariant." A sign only signifies an object to an
Interpretant (an agent). Without the third bit (the Interpretant),
the connection between sign and object is a dead pointer. Meaning is
a three-way constraint satisfaction problem (Sat).

Invariant: Meaning requires a Triad.
Gap: The "Binary" trap—assuming meaning is a direct property of the object or the sign.
Projection: Tripartite Aeonic Extension Witness (Gnosis.Witnesses.Gnostic.TripartiteAeonicExtensionWitness).
-/

inductive SemioticComponent where
  | sign         : SemioticComponent
  | object       : SemioticComponent
  | interpretant : SemioticComponent
  deriving DecidableEq

def meaningSat (components : List SemioticComponent) : Bool :=
  components.contains .sign ∧
  components.contains .object ∧
  components.contains .interpretant

/--
Anti-Theory Witness: A binary set (Sign, Object) fails to satisfy
the meaning constraint. Only the Triad is Sat.
-/
theorem semiotic_triad_necessity :
    meaningSat [.sign, .object] = false ∧
    meaningSat [.sign, .object, .interpretant] = true := by
  unfold meaningSat
  constructor <;> exact (by decide)

end Gnosis.Witnesses.History
