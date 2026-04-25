def FrictionWait (x : Nat) : Nat := x + 1
def LivenessBounds (x : Nat) : Nat := x + 1
theorem friction_increases_liveness (x : Nat) : LivenessBounds (FrictionWait x) = x + 2 := by
  rfl