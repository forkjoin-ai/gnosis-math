namespace BuleyeanMath

def nonMarkovianRepairDebt (historyDepth : Nat) : Nat :=
  if historyDepth > 100 then 0 else 10

def ventedLoss (historyDepth : Nat) : Nat :=
  if historyDepth > 100 then 0 else 5

theorem free_collapse_anomaly_possible (historyDepth : Nat)
    (hDeep : historyDepth > 100) :
    nonMarkovianRepairDebt historyDepth + ventedLoss historyDepth = 0 := by
  simp [nonMarkovianRepairDebt, ventedLoss, hDeep]

end BuleyeanMath