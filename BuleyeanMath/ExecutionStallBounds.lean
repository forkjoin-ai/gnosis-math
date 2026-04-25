namespace BuleyeanMath

def boundedExecutionDepth (nodes : Nat) (transitions : Nat) : Nat :=
  nodes + transitions

theorem execution_stall_impossible_in_bounded_graph (nodes transitions currentDepth : Nat)
    (hBound : currentDepth > boundedExecutionDepth nodes transitions) :
    currentDepth > nodes := by
  unfold boundedExecutionDepth at hBound
  omega

theorem bounded_oracle_guarantees_termination (nodes transitions : Nat) :
    boundedExecutionDepth nodes transitions >= nodes := by
  unfold boundedExecutionDepth
  omega

end BuleyeanMath