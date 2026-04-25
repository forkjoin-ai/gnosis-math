
open Filter MeasureTheory
open scoped BigOperators ENNReal Matrix

namespace BuleyeanMath

namespace TwoNodeAdaptiveRoutingParameters

variable (params : TwoNodeAdaptiveRoutingParameters)

theorem candidate_eq_constructiveThroughput_toReal :
    ∀ i, (params.ceilingTrafficData.constructiveThroughput i).toReal = params.candidate i := by
  intro i
  exact params.ceilingTrafficData.constructiveThroughput_toReal_eq_real_fixed_point
    params.ceiling_spectralRadius_lt_one
    params.candidate
    params.candidate_nonneg
    params.candidate_fixed_point
    i

