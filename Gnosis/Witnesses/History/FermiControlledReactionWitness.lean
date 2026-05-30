import Gnosis.GnosisMath.Basic

namespace Gnosis.Witnesses.History

/--
Enrico Fermi: The Controlled Reaction Witness.
Chicago, 1942.

Contrarian Take: A nuclear explosion is a computation that enters an
infinite loop (exponential runaway) until the hardware (the fuel) is
consumed. The "Nuclear Pile" was the first implementation of a
"Controlled Loop" with a hardware-level `break` statement (the control rods).
Fermi proved that you can extract energy from the vacuum by running
a reaction at the "Edge of Criticality"—the exact point where the
multiplication factor `k = 1`.

Invariant: Stability requires `k = 1`.
Gap: The "Binary" trap—assuming a reaction is either "off" or "exploding."
Projection: Stability Infty Categories (Gnosis.StableInftyCategories).
-/

def multiplicationFactor (controlRodDepth : Nat) : Int :=
  10 - (controlRodDepth : Int)

def isStable (k : Int) : Bool :=
  k == 1

/--
Anti-Theory Witness: Stability is only achieved at a specific depth
where the multiplication factor exactly matches the decay.
-/
theorem fermi_criticality_witness :
    isStable (multiplicationFactor 9) = true ∧
    isStable (multiplicationFactor 0) = false := by
  unfold isStable multiplicationFactor
  constructor <;> exact (by decide)

end Gnosis.Witnesses.History
