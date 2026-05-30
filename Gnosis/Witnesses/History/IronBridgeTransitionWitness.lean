import Gnosis.GnosisMath.Basic

namespace Gnosis.Witnesses.History

/--
The Iron Bridge: The Material Transition Witness.
Coalbrookdale, 1779.

Contrarian Take: The Industrial Revolution was not just a "technological
advance." It was a "State-Transition of the Substrate." Before 1779,
the world was built on a "Biological/Geological Grid" (Wood, Stone).
The Iron Bridge marked the transition to a "Synthetic/Infinite Grid" (Iron).
Iron is a material constant that does not decay like wood or crumble like
stone. It allowed for an unbundling of structure from the limits of
the biological clock.

Invariant: Structure is a function of the material constant.
Gap: The "Scarcity" trap—assuming building is limited by the growth-rate of trees.
Projection: Iron Bridge Stub (Gnosis.IronBridgeStub).
-/

inductive MaterialSubstrate where
  | wood : MaterialSubstrate
  | iron : MaterialSubstrate
  deriving DecidableEq

def decayRate (m : MaterialSubstrate) : Nat :=
  match m with
  | .wood => 10
  | .iron => 0 -- Simplified constant

/--
Anti-Theory Witness: The transition to iron provides a zero-decay
constant for the structural manifold.
-/
theorem iron_transition_witness :
    decayRate .iron < decayRate .wood := by
  unfold decayRate
  exact (by decide)

end Gnosis.Witnesses.History
