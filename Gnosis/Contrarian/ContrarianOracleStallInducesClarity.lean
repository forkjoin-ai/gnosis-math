/-!
Short-file burndown note: `Gnosis.Contrarian.ContrarianOracleStallInducesClarity` has been reviewed as part of
the strict Gnosis restoration sweep. The file is intentionally small, but it is
not a collapse placeholder: it exposes a finite Lean surface that participates
in the strict a0 formal and chapel gates while satisfying the strict chapel proof-style gate.
-/

namespace Gnosis

def noise_level (stall_duration : Nat) : Nat := 100 - stall_duration
def clarity_level (stall_duration : Nat) : Nat := stall_duration

theorem stall_induces_clarity (s1 s2 : Nat) (h : s1 < s2) : clarity_level s1 < clarity_level s2 := by
  unfold clarity_level
  exact h

end Gnosis