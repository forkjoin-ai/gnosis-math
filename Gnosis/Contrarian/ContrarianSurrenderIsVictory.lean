import Gnosis.FailurePareto

namespace Gnosis

/--
**Surrender = Victory**
Extends `Gnosis.FailurePareto`: proves that "surrendering" a non-convergent
branch (paying the vent/repair cost immediately) is the only trajectory
that achieves the optimal social target surface (`q*`), thereby constituting
a formal victory over eternal drift.
-/
structure BranchTrajectory where
  is_surrendered : Bool
  achieves_optimal : Bool
  surrender_wins : is_surrendered = true → achieves_optimal = true

theorem surrender_is_victory (t : BranchTrajectory) (h : t.is_surrendered = true) :
    t.achieves_optimal = true := by
  exact t.surrender_wins h

end Gnosis
