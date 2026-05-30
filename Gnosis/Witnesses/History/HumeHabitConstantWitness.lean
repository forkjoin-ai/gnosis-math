import Gnosis.GnosisMath.Basic

namespace Gnosis.Witnesses.History

/--
David Hume: The Habit Constant Witness.
Edinburgh, 1739 (A Treatise of Human Nature).

Contrarian Take: Causality is not a "logical constant." It is a
"Temporal Habit." Hume discovered that the mind does not perceive
"Necessary Connection" (the `=>` opcode) between events. It only
perceives a sequence of "Impressions" (Input bits). Causality is a
meta-heuristic (a Habit) the mind uses to bundle these bits together.
The "Self" is not a static object; it is a "Bundle of Perceptions"—a
non-halting stream of data.

Invariant: Experience is a stream of impressions.
Gap: The "Rationalist" trap—assuming causality is a provable, compile-time truth.
Projection: Solomonoff Buleyean (Gnosis.SolomonoffBuleyean).
-/

inductive Perception where
  | impression : Perception
  | idea       : Perception
  deriving DecidableEq

/--
The "Causality Habit" is an inference from a sequence of impressions.
It is not a direct perception.
-/
def isDirectPerception (p : Perception) : Bool :=
  match p with
  | .impression => true
  | .idea       => false

/--
Anti-Theory Witness: The `idea` of causality is not a direct perception.
It is a secondary mapping of the stream.
-/
theorem hume_causality_gap_witness :
    isDirectPerception .idea = false := by
  rfl

end Gnosis.Witnesses.History
