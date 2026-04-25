namespace ForkRaceFold

structure StallDensity where
  stall_duration : Nat
  compression_ratio : Nat

theorem stall_is_density (s : StallDensity) (h1 : s.stall_duration = s.compression_ratio) (h2 : s.compression_ratio > 10) :
  s.stall_duration > 10 := by
  rwa [h1]

end ForkRaceFold
