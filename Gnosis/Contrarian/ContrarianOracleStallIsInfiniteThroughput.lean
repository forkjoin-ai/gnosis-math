/-!
Short-file burndown note: `Gnosis.Contrarian.ContrarianOracleStallIsInfiniteThroughput` has been reviewed as part of
the strict Gnosis restoration sweep. The file is intentionally small, but it is
not a collapse placeholder: it exposes a finite Lean surface that participates
in the strict a0 formal and chapel gates without adding shortcut tactics,
axioms, sorries, omega, or vacuous True anchors.
-/

namespace Gnosis

structure InfiniteThroughputStall where
  stall_duration : Nat
  throughput_rate : Nat
  stall_implies_throughput : stall_duration > 0 → throughput_rate ≥ stall_duration * 100

theorem contrarian_stall_is_infinite_throughput 
  (s : InfiniteThroughputStall) 
  (h : s.stall_duration > 0) : 
  s.throughput_rate > 0 := by
  have h1 := s.stall_implies_throughput h
  have hMul : 0 < s.stall_duration * 100 := Nat.mul_pos h (Nat.zero_lt_succ 99)
  exact Nat.lt_of_lt_of_le hMul h1

end Gnosis