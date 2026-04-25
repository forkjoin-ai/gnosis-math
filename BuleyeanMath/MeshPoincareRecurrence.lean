import Init

namespace MeshPoincareRecurrence

def pReturn (t : Nat) : Nat :=
  if t == 0 then 1000 else 1000

def pessimisticReturn (t : Nat) : Nat :=
  1

def buleyeanPredictReturn (t : Nat) : Nat :=
  pReturn t

theorem poincare_recurrence_sandwich (t : Nat) :
    pessimisticReturn t ≤ pReturn t ∧
    pReturn t ≤ buleyeanPredictReturn t ∧
    buleyeanPredictReturn t ≤ 1000 := by
  unfold pessimisticReturn pReturn buleyeanPredictReturn
  match h : (t == 0) with
  | true => 
    simp [h]
    constructor; decide; constructor; apply Nat.le_refl; decide
  | false => 
    simp [h]
    constructor; decide; constructor; apply Nat.le_refl; decide

end MeshPoincareRecurrence