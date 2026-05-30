import Gnosis.GnosisMath.Basic

namespace Gnosis.Witnesses.History

inductive WitnessFrame where
  | thief
  | wife
  | samurai
  | woodcutter
  deriving DecidableEq

def reportedState (f : WitnessFrame) : Nat :=
  match f with
  | .thief      => 1
  | .wife       => 2
  | .samurai    => 3
  | .woodcutter => 4

theorem rashomon_divergence_witness : ∀ (f1 f2 : WitnessFrame), f1 ≠ f2 → reportedState f1 ≠ reportedState f2
  | .thief, .thief, h => (h rfl).elim
  | .thief, .wife, _ => by decide
  | .thief, .samurai, _ => by decide
  | .thief, .woodcutter, _ => by decide
  | .wife, .thief, _ => by decide
  | .wife, .wife, h => (h rfl).elim
  | .wife, .samurai, _ => by decide
  | .wife, .woodcutter, _ => by decide
  | .samurai, .thief, _ => by decide
  | .samurai, .wife, _ => by decide
  | .samurai, .samurai, h => (h rfl).elim
  | .samurai, .woodcutter, _ => by decide
  | .woodcutter, .thief, _ => by decide
  | .woodcutter, .wife, _ => by decide
  | .woodcutter, .samurai, _ => by decide
  | .woodcutter, .woodcutter, h => (h rfl).elim

end Gnosis.Witnesses.History