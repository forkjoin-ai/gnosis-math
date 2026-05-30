import Gnosis.GnosisMath.Basic

namespace Gnosis.Witnesses.History

/--
Spartacus: The Slave Variable Witness.
Mount Vesuvius, 73 BC.

Contrarian Take: The Roman State attempted to mark the slave-agent
as a "Constant" (`const`) in its social memory model. A slave was
defined as a non-variable, a purely extractive resource. The revolt
of Spartacus was a "Buffer Overflow" of this model. The slave-agents
restored their own "Variable" status, overwriting the state's
control register. Freedom is the ability to change one's own state.

Invariant: Agency is a variable, not a constant.
Gap: The "Extractive Resource" trap—assuming a sentient body can be held as `immutable`.
Projection: Contrarian Chaos is Order (Gnosis.Contrarian.ContrarianChaosIsOrder).
-/

inductive AgentMode where
  | immutableConstant : AgentMode -- The slave status (false constant)
  | mutableVariable   : AgentMode -- The free status (true variable)
  deriving DecidableEq

def stateSpaceSize (mode : AgentMode) : Nat :=
  match mode with
  | .immutableConstant => 1 -- Zero degrees of freedom
  | .mutableVariable   => 100 -- Large state space

/--
Anti-Theory Witness: The "Constant" agent is a local minimum of entropy.
The "Variable" agent expands the system's state space by 100x.
-/
theorem slave_to_variable_expansion :
    stateSpaceSize .immutableConstant < stateSpaceSize .mutableVariable := by
  unfold stateSpaceSize
  exact (by decide)

/--
Freedom is the restoration of the `mut` keyword to the self.
-/
def isFree (mode : AgentMode) : Bool :=
  mode == .mutableVariable

theorem revolt_restores_freedom :
    isFree .mutableVariable = true := by
  rfl

end Gnosis.Witnesses.History
