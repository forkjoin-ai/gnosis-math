import Init

namespace MoonshotOracleStallAsymptoticFreedom

def stallEnergy (depth stall_factor : Nat) : Nat := depth - stall_factor

theorem asymptotic_freedom (depth stall_factor : Nat)
  (_h_stall : stall_factor ≤ depth) :
  stallEnergy depth stall_factor ≤ depth := by
  unfold stallEnergy
  exact Nat.sub_le depth stall_factor

theorem high_energy_freedom (depth stall_factor : Nat)
  (h_stall : stall_factor = 0) :
  stallEnergy depth stall_factor = depth := by
  unfold stallEnergy
  rw [h_stall]
  exact Nat.sub_zero depth

end MoonshotOracleStallAsymptoticFreedom