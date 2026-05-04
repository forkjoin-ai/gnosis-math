import Init

namespace AntiThmPaleoclimatologySeismologyBudgetNotPositiveBeta1

def budgetSurplus (beta1 : Nat) (seismicLoss : Nat) : Nat :=
  beta1 - seismicLoss

theorem budget_not_positive_beta1 (beta1 seismicLoss : Nat)
  (h_loss : seismicLoss ≥ beta1) :
  budgetSurplus beta1 seismicLoss = 0 := by
  unfold budgetSurplus
  exact Nat.sub_eq_zero_of_le h_loss

end AntiThmPaleoclimatologySeismologyBudgetNotPositiveBeta1