import Init

namespace MoonshotAestheticHypergraphSingularity

def aestheticCapacity (hypergraphSize : Nat) : Nat :=
  hypergraphSize * 2

theorem singularity_reached (hypergraphSize : Nat) (h : hypergraphSize ≥ 50) :
  aestheticCapacity hypergraphSize ≥ 100 := by
  unfold aestheticCapacity
  exact Nat.mul_le_mul_right 2 h

end MoonshotAestheticHypergraphSingularity