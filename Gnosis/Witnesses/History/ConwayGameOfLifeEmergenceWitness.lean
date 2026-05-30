import Gnosis.GnosisMath.Basic

namespace Gnosis.Witnesses.History

/--
John Horton Conway: The Game of Life Emergence Witness.
Liverpool/Cambridge, 1970.

Contrarian Take: "Life" is a hallucination of the observer. The system
is just a 2D cellular automaton enforcing a 3-agent neighborhood constraint.
Complexity is not "added" to the system; it is what remains when the rules
fail to collapse the state space to zero (death) or expand it to infinity (chaos).
Life is a metastable local minimum between vacuum and heat-death.

Invariant: Complexity requires a specific neighborhood weight (exactly 3).
Gap: The "Vitalism" trap—assuming life requires a non-computational essence.
Projection: Finite Dynamics Core (Gnosis.FiniteDynamicsCore).
-/

inductive CellState where
  | vacuum : CellState
  | alive  : CellState
  deriving DecidableEq

def nextState (current : CellState) (neighbors : Nat) : CellState :=
  match current with
  | .alive => if neighbors = 2 ∨ neighbors = 3 then .alive else .vacuum
  | .vacuum => if neighbors = 3 then .alive else .vacuum

/--
Anti-Theory Witness: The vacuum ONLY produces life when neighbors are exactly 3.
Any other input preserves the vacuum.
-/
theorem vacuum_stability_breach (n : Nat) (h : n ≠ 3) :
    nextState .vacuum n = .vacuum := by
  unfold nextState
  exact if_neg h

/--
The "Glider" exists because the rule set allows a non-zero residue.
-/
theorem existence_of_emergence :
    nextState .vacuum 3 = .alive := by
  rfl

end Gnosis.Witnesses.History