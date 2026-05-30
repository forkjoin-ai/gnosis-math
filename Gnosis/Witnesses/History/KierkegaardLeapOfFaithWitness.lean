import Gnosis.GnosisMath.Basic

namespace Gnosis.Witnesses.History

/--
Søren Kierkegaard: The Leap of Faith Witness.
Copenhagen, 1843.

Contrarian Take: Faith is not a "conclusion" of logic. It is the
"Early Exit" from the logic-engine. If an agent waits for a purely
rational proof for existence, they will never act (infinite loop).
The "Leap" is a `break` statement that terminates the search space
of the intellect to allow the execution of the soul.
Anxiety (Angst) is the vertigo of seeing the infinite possible branches.

Invariant: Action requires termination.
Gap: The "Intellectualism" trap—assuming logic can resolve its own halting problem.
Projection: Oracle Execution Stall Breakthrough (Gnosis.Oracle.OracleExecutionStallBreakthrough).
-/

inductive SearchMode where
  | infiniteLogicalLoop : SearchMode
  | leapOfAction         : SearchMode
  deriving DecidableEq

def hasTerminated (mode : SearchMode) : Bool :=
  match mode with
  | .infiniteLogicalLoop => false
  | .leapOfAction         => true

/--
Anti-Theory Witness: The Leap provides termination (Sat) where logic
provides only a non-halting search.
-/
theorem leap_terminates_search :
    hasTerminated .leapOfAction ≠ hasTerminated .infiniteLogicalLoop := by
  exact (by decide)

end Gnosis.Witnesses.History
