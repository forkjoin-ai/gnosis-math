import BuleyeanMath.Tactics
import BuleyeanMath.Real

open BuleyeanMath

namespace ContrarianObservabilityDegrades

structure SystemState where
  true_performance : BuleReal
  observed_performance : BuleReal
  observer_effect : observed_performance < true_performance

theorem observability_loss (s : SystemState) :
  s.observed_performance < s.true_performance := by
  exact s.observer_effect

end ContrarianObservabilityDegrades