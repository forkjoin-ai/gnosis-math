import Gnosis.GnosisMath.Basic

namespace Gnosis.Witnesses.History

/--
Martin Heidegger: The Dasein Temporal Witness.
Meßkirch, 1927 (Being and Time).

Contrarian Take: "Being" is not a static object in space. It is a
temporal "Clearing" (Lichtung). "Dasein" is the agent that is
constituted by its own temporal deficit—the recognition of its
finite runtime ("Being-towards-death"). Truth is not a Sat solution,
but an "Unconcealment" (Aletheia) that occurs within this clearing.
Existence is the process of resolving the deficit between the
thrown-ness of the past and the projection of the future.

Invariant: Existence is temporal resolution.
Gap: The "Ontotheology" trap—assuming Being is a permanent substance.
Projection: Pleromatic Evolution Resolution (Gnosis.PleromaticEvolutionResolution).
-/

inductive TemporalMode where
  | staticSubstance : TemporalMode -- The false view of Being
  | temporalClearing : TemporalMode -- Dasein (the true view)
  deriving DecidableEq

/--
The "Deficit" of a temporal mode.
A static substance has no deficit (it is "dead").
A temporal clearing has a positive deficit (it is "alive" and running).
-/
def temporalDeficit (tm : TemporalMode) : Nat :=
  match tm with
  | .staticSubstance  => 0
  | .temporalClearing => 1

/--
Anti-Theory Witness: Dasein is defined by its non-zero temporal deficit.
To exist is to have a pending halt.
-/
theorem dasein_existence_witness :
    0 < temporalDeficit .temporalClearing := by
  unfold temporalDeficit
  exact (by decide)

end Gnosis.Witnesses.History
