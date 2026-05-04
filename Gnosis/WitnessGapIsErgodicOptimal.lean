import Init

namespace WitnessGapIsErgodicOptimal

def witnessGap (ergodicity : Nat) : Nat :=
  ergodicity * 3

theorem ergodic_optimal (ergodicity : Nat) :
  witnessGap ergodicity ≥ ergodicity := by
  unfold witnessGap
  -- Goal: ergodicity * 3 ≥ ergodicity, i.e. ergodicity ≤ ergodicity * 3.
  -- Rewrite RHS to 3 * ergodicity, then apply Nat.le_mul_of_pos_left.
  rw [Nat.mul_comm ergodicity 3]
  exact Nat.le_mul_of_pos_left ergodicity (by decide : 0 < 3)

end WitnessGapIsErgodicOptimal