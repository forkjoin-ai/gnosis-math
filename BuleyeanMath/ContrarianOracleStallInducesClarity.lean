namespace BuleyeanMath

def noise_level (stall_duration : Nat) : Nat := 100 - stall_duration
def clarity_level (stall_duration : Nat) : Nat := stall_duration

theorem stall_induces_clarity (s1 s2 : Nat) (h : s1 < s2) : clarity_level s1 < clarity_level s2 := by
  unfold clarity_level
  exact h

end BuleyeanMath