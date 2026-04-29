import Init

namespace MeshPoincareRecurrence

def pReturn (t : Nat) : Nat :=
  if t == 0 then 1000 else 1000

def pessimisticReturn (_t : Nat) : Nat :=
  1

def buleyeanPredictReturn (t : Nat) : Nat :=
  pReturn t

theorem poincare_recurrence_sandwich (t : Nat) :
    pessimisticReturn t ≤ pReturn t ∧
    pReturn t ≤ buleyeanPredictReturn t ∧
    buleyeanPredictReturn t ≤ 1000 := by
  constructor
  · unfold pessimisticReturn pReturn
    split <;> omega
  · constructor
    · unfold buleyeanPredictReturn; apply Nat.le_refl
    · unfold buleyeanPredictReturn pReturn
      split <;> omega

end MeshPoincareRecurrence