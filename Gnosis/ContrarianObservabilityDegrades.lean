import Gnosis.Tactics
import Gnosis.Real

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