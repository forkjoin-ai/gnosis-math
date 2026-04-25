namespace BuleyeanMath

structure InfiniteThroughputStall where
  stall_duration : Nat
  throughput_rate : Nat
  stall_implies_throughput : stall_duration > 0 → throughput_rate ≥ stall_duration * 100

theorem contrarian_stall_is_infinite_throughput 
  (s : InfiniteThroughputStall) 
  (h : s.stall_duration > 0) : 
  s.throughput_rate > 0 := by
  have h1 := s.stall_implies_throughput h
  omega

end BuleyeanMath