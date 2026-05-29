import Init

namespace CrossDomainPalaeontologyCryptographicStallBridge

def cryptographicStall (fossilAge : Nat) (shield : Nat) : Nat :=
  fossilAge + shield

theorem stall_bridge_bounded (fossilAge : Nat) (shield : Nat) :
  cryptographicStall fossilAge shield ≥ fossilAge := by
  unfold cryptographicStall
  exact Nat.le_add_right fossilAge shield

end CrossDomainPalaeontologyCryptographicStallBridge