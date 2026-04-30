import Init

namespace Gnosis

/-!
  # Deficit-Capacity Duality (Information Bottleneck)
  
  This module formalizes the topological relationship between computation 
  complexity and transport capacity. It serves as the canonical source for 
  `topologicalDeficit` and its monotonicity properties.
-/

/-- Computation Complexity: The first Betti number β₁ of an N-path graph. -/
def computationComplexity (N : Nat) : Nat :=
  N - 1

/-- Transport Capacity: The first Betti number β₁ of a C-stream transport layer. -/
def transportCapacity (C : Nat) : Nat :=
  C - 1

/-- Topological Deficit: The signed mismatch between complexity and capacity. -/
def topologicalDeficit (N C : Nat) : Int :=
  (computationComplexity N : Int) - (transportCapacity C : Int)

/-- Deficit is zero when capacity matches complexity exactly. -/
theorem deficit_zero_at_saturation (N : Nat) :
    topologicalDeficit N N = 0 := by
  unfold topologicalDeficit computationComplexity transportCapacity
  omega

/-- Deficit is monotonically increasing as computation complexity increases. -/
theorem deficit_monotonicity_N (N1 N2 C : Nat) (h : N1 ≤ N2) :
    topologicalDeficit N1 C ≤ topologicalDeficit N2 C := by
  unfold topologicalDeficit computationComplexity transportCapacity
  omega

/-- Deficit is monotonically decreasing as transport capacity increases. -/
theorem deficit_monotonicity_C (N C1 C2 : Nat) (h : C1 ≤ C2) :
    topologicalDeficit N C2 ≤ topologicalDeficit N C1 := by
  unfold topologicalDeficit computationComplexity transportCapacity
  omega

/-- The "Information Bottleneck": deficit is non-negative if complexity exceeds capacity. -/
theorem deficit_non_negative_if_complexity_exceeds_capacity (N C : Nat) (h : N ≥ C) :
    topologicalDeficit N C ≥ 0 := by
  unfold topologicalDeficit computationComplexity transportCapacity
  omega

/-- Maximum bottleneck: when capacity is minimal (1 stream), deficit equals N-1. -/
theorem capacity_bottleneck_maximal (N : Nat) (h : N > 0) :
    topologicalDeficit N 1 = (N : Int) - 1 := by
  unfold topologicalDeficit computationComplexity transportCapacity
  omega

end Gnosis
