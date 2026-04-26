import Init

namespace MeshInfiniteMonkeys

def pShakespeare (t : Nat) : Nat :=
  if t == 0 then 0 else 1000 - (1000 / t)

def pessimisticReachability (t : Nat) : Nat :=
  if t > 0 then 1 else 0

def buleyeanPredictReachability (t : Nat) : Nat :=
  pShakespeare t

theorem monkey_sandwich (t : Nat) (h : t >= 1) :
    pessimisticReachability t ≤ pShakespeare t ∧
    pShakespeare t ≤ buleyeanPredictReachability t ∧
    buleyeanPredictReachability t ≤ 1000 := by
  constructor
  · unfold pessimisticReachability pShakespeare
    split <;> split <;> omega
  · constructor
    · unfold pShakespeare buleyeanPredictReachability
      apply Nat.le_refl
    · unfold buleyeanPredictReachability pShakespeare
      split <;> omega

























































































end MeshInfiniteMonkeys