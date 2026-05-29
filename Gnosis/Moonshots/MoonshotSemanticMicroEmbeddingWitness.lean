namespace ForkRaceFold

structure MicroEmbedding where
  gap_size : ℕ

theorem witness_gap_always_bounded (m : MicroEmbedding) : m.gap_size ≥ 0 := by
  exact Nat.zero_le m.gap_size

end ForkRaceFold