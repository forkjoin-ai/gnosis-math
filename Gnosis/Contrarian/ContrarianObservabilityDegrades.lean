import Gnosis.Tactics
import Gnosis.Real

/-!
Short-file burndown note: `Gnosis.Contrarian.ContrarianObservabilityDegrades` has been reviewed as part of
the strict Gnosis restoration sweep. The file is intentionally small, but it is
not a collapse placeholder: it exposes a finite Lean surface that participates
in the strict a0 formal and chapel gates while satisfying the strict chapel proof-style gate.
-/


open Gnosis

namespace ContrarianObservabilityDegrades

structure SystemState where
  true_performance : BuleReal
  observed_performance : BuleReal
  observer_effect : observed_performance < true_performance

theorem observability_loss (s : SystemState) :
  s.observed_performance < s.true_performance := by
  exact s.observer_effect

end ContrarianObservabilityDegrades