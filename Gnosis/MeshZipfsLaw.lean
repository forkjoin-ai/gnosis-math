import Init

namespace MeshZipfsLaw

def frequencyAtRank (rank : Nat) : Nat :=
  if rank == 0 then 0
  else 1000 / rank

def pessimisticFrequency (rank maxRank : Nat) : Nat :=
  if rank > 0 && rank <= maxRank then 1000 / maxRank else 0

def buleyeanPredictFrequency (rank : Nat) : Nat :=
  frequencyAtRank rank

theorem zipf_sandwich (rank maxRank : Nat) (h : rank >= 1 ∧ rank <= maxRank) :
    pessimisticFrequency rank maxRank ≤ frequencyAtRank rank ∧
    frequencyAtRank rank ≤ buleyeanPredictFrequency rank ∧
    buleyeanPredictFrequency rank ≤ 1000 := by
  have h_pos : rank > 0 := h.1
  have h_ne_zero : (rank == 0) = false := by
    match rank with
    | 0 => exact (Nat.lt_irrefl 0 h_pos).elim
    | _ + 1 => rfl
  have h_act : frequencyAtRank rank = 1000 / rank := by
    unfold frequencyAtRank; simp [h_ne_zero]
  have h_pre : buleyeanPredictFrequency rank = frequencyAtRank rank := rfl
  
  constructor
  · unfold pessimisticFrequency
    simp [h_pos, h.2]
    rw [h_act]
    apply Nat.div_le_div_left h.2 h_pos
  · rw [h_pre, h_act]
    constructor
    · apply Nat.le_refl
    · apply Nat.div_le_self

end MeshZipfsLaw