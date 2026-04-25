import Lean

namespace ForkRaceFold

variable (Architecture : Type)
variable (InterpretationLayerMissing : Architecture → Prop)
variable (Redundancy : Architecture → Prop)
variable (Resilience : Architecture → Prop)

theorem contrarian_interpretation_missing_redundancy (a : Architecture)
  (h_missing : InterpretationLayerMissing a)
  (h_provides_redundancy : InterpretationLayerMissing a → Redundancy a)
  (h_redundancy_resilience : Redundancy a → Resilience a) :
  Resilience a := by
  apply h_redundancy_resilience
  apply h_provides_redundancy
  exact h_missing

end ForkRaceFold