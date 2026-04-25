import Init

namespace MoonshotOracleStallAsymptoticFreedom

def stallEnergy (depth stall_factor : Nat) : Nat := depth - stall_factor

theorem asymptotic_freedom (depth stall_factor : Nat)
  (h_stall : stall_factor ≤ depth) :
  stallEnergy depth stall_factor ≤ depth := by
  unfold stallEnergy
  omega

theorem high_energy_freedom (depth stall_factor : Nat)
  (h_stall : stall_factor = 0) :
  stallEnergy depth stall_factor = depth := by
  unfold stallEnergy
  omega

end MoonshotOracleStallAsymptoticFreedom