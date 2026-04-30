set_option linter.unusedVariables false

namespace Gnosis

def historicalDebt (initialDebt cycles decayRate : Nat) : Nat :=
  if decayRate == 0 then initialDebt else initialDebt / (cycles + 1)

theorem incomplete_ergodicity_retains_debt (initialDebt cycles : Nat)
    (hInitial : initialDebt > 0) :
    historicalDebt initialDebt cycles 0 = initialDebt := by
  unfold historicalDebt
  rfl

theorem perpetual_attractor_blocker (initialDebt cycles : Nat)
    (hInitial : initialDebt > 0) :
    historicalDebt initialDebt cycles 0 > 0 := by
  simpa [historicalDebt] using hInitial

end Gnosis