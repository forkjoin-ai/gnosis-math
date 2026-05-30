import Gnosis.GnosisMath.Basic

namespace Gnosis.Witnesses.History

/--
Jean-Paul Sartre: The Self-Choice Witness.
Paris, 1943 (Being and Nothingness).

Contrarian Take: The "Self" is not a compile-time constant. It is a
"Runtime Variable." "Existence precedes Essence" means the agent is
initialized with a null identity (the Void). The agent's identity is
the cumulative sum of its choices (state transitions). Nausea is the
vertigo of recognizing that there is no "Default Configuration" for
the human agent; we must compile our own essence on the fly.

Invariant: Freedom is the ability to mutate the self's config.
Gap: The "Essentialist" trap—assuming identity is a fixed, immutable bit.
Projection: Contrarian Nothingness is Meaning (Gnosis.Contrarian.ContrarianNothingnessIsMeaning).
-/

inductive EssenceMode where
  | fixedConstant  : EssenceMode -- The Essentialist View
  | runtimeVariable : EssenceMode -- The Existentialist View
  deriving DecidableEq

def configMutationsAllowed (m : EssenceMode) : Nat :=
  match m with
  | .fixedConstant   => 0
  | .runtimeVariable => 100 -- Arbitrary large variety

/--
Anti-Theory Witness: The Existentialist mode allows for strict mutation
of the agent's identity, whereas the Essentialist mode is a dead-lock.
-/
theorem sartre_freedom_expansion :
    configMutationsAllowed .fixedConstant < configMutationsAllowed .runtimeVariable := by
  unfold configMutationsAllowed
  exact (by decide)

end Gnosis.Witnesses.History
