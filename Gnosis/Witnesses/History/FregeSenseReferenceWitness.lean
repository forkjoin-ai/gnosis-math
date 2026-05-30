import Gnosis.GnosisMath.Basic

namespace Gnosis.Witnesses.History

/--
Gottlob Frege: The Sense-Reference Witness.
Jena, 1892 (Über Sinn und Bedeutung).

Contrarian Take: Identity (`a = b`) is not a simple boolean comparison
of addresses. It is a mapping between "Sense" (the route to the address)
and "Reference" (the value at the address). Two different routes can
point to the same value, but they contain different information (Sense).
The "Morning Star" and the "Evening Star" are the same reference (Venus),
but different senses. Informational content is route-dependent.

Invariant: Reference is route-invariant; Sense is route-specific.
Gap: The "Extensionality" trap—assuming only the final value matters.
Projection: Foundations of Arithmetic (Gnosis.Jena.FregeStub).
-/

inductive Sense where
  | morningStar : Sense
  | eveningStar : Sense
  deriving DecidableEq

def reference (s : Sense) : Nat :=
  match s with
  | .morningStar => 1 -- Venus
  | .eveningStar => 1 -- Venus

/--
Anti-Theory Witness: The references are identical (a = b), but the
senses are distinct (a ≠ b). Information exists in the Sense.
-/
theorem frege_identity_split :
    reference .morningStar = reference .eveningStar ∧ Sense.morningStar ≠ Sense.eveningStar := by
  constructor
  · rfl
  · exact (by decide)

end Gnosis.Witnesses.History
