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
  exact Int.sub_self _

/-- Deficit is monotonically increasing as computation complexity increases. -/
theorem deficit_monotonicity_N (N1 N2 C : Nat) (h : N1 ≤ N2) :
    topologicalDeficit N1 C ≤ topologicalDeficit N2 C := by
  unfold topologicalDeficit computationComplexity transportCapacity
  exact Int.sub_le_sub_right (Int.ofNat_le.mpr (Nat.sub_le_sub_right h 1)) _

/-- Deficit is monotonically decreasing as transport capacity increases. -/
theorem deficit_monotonicity_C (N C1 C2 : Nat) (h : C1 ≤ C2) :
    topologicalDeficit N C2 ≤ topologicalDeficit N C1 := by
  unfold topologicalDeficit computationComplexity transportCapacity
  exact Int.sub_le_sub_left (Int.ofNat_le.mpr (Nat.sub_le_sub_right h 1)) _

/-- The "Information Bottleneck": deficit is non-negative if complexity exceeds capacity. -/
theorem deficit_non_negative_if_complexity_exceeds_capacity (N C : Nat) (h : N ≥ C) :
    topologicalDeficit N C ≥ 0 := by
  unfold topologicalDeficit computationComplexity transportCapacity
  exact Int.sub_nonneg.mpr (Int.ofNat_le.mpr (Nat.sub_le_sub_right h 1))

/-- Maximum bottleneck: when capacity is minimal (1 stream), deficit equals N-1. -/
theorem capacity_bottleneck_maximal (N : Nat) (h : N > 0) :
    topologicalDeficit N 1 = (N : Int) - 1 := by
  unfold topologicalDeficit computationComplexity transportCapacity
  show ((N - 1 : Nat) : Int) - ((1 - 1 : Nat) : Int) = (N : Int) - 1
  rw [show (1 - 1 : Nat) = 0 from rfl, Int.ofNat_zero, Int.sub_zero,
      Int.ofNat_sub h]
  rfl

/-- Compatibility name used by the older transport/causality modules. -/
theorem tcp_deficit_is_path_count_minus_one
    {pathCount : Nat}
    (hPaths : 1 ≤ pathCount) :
    topologicalDeficit pathCount 1 = (pathCount : Int) - 1 := by
  exact capacity_bottleneck_maximal pathCount hPaths

/-- Compatibility name for the zero-deficit frontier witness. -/
theorem matched_deficit_is_zero
    {pathCount : Nat}
    (_hPaths : 1 ≤ pathCount) :
    topologicalDeficit pathCount pathCount = 0 := by
  exact deficit_zero_at_saturation pathCount

/-- Compatibility name for transport-side deficit monotonicity. -/
theorem deficit_monotone_in_streams
    {pathCount s1 s2 : Nat}
    (_hS1 : 1 ≤ s1)
    (hS : s1 ≤ s2) :
    topologicalDeficit pathCount s2 ≤ topologicalDeficit pathCount s1 := by
  exact deficit_monotonicity_C pathCount s1 s2 hS

/-- Any system with more paths than a single stream carries a positive deficit. -/
theorem single_stream_deficit_positive
    {pathCount : Nat}
    (hPaths : 2 ≤ pathCount) :
    0 < topologicalDeficit pathCount 1 := by
  unfold topologicalDeficit computationComplexity transportCapacity
  show 0 < ((pathCount - 1 : Nat) : Int) - ((1 - 1 : Nat) : Int)
  rw [show (1 - 1 : Nat) = 0 from rfl, Int.ofNat_zero, Int.sub_zero]
  exact Int.natCast_pos.mpr (Nat.sub_pos_of_lt hPaths)

/-- Matching or exceeding the path count eliminates positive deficit. -/
theorem deficit_nonpositive_when_streams_cover_paths
    {pathCount transportStreams : Nat}
    (hCover : pathCount ≤ transportStreams) :
    topologicalDeficit pathCount transportStreams ≤ 0 := by
  unfold topologicalDeficit computationComplexity transportCapacity
  exact Int.sub_nonpos_of_le (Int.ofNat_le.mpr (Nat.sub_le_sub_right hCover 1))

end Gnosis
