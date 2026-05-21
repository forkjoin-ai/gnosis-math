import Gnosis.ComteObservationErrorMonotonicity

/-
  ComteObservationErrorOrder.lean
  =================================

  Burns down the next-exploration target from
  `ComteObservationErrorMonotonicity`: a reusable preorder over
  observation surfaces with equal measurement counts and non-increasing
  prediction error.

  Imports `Gnosis.ComteObservationErrorMonotonicity`. Zero `sorry`,
  zero new `axiom`.
-/

namespace Gnosis
namespace ComteObservationErrorOrder

open ComtePositiveEmpirics
open ComteObservationErrorMonotonicity

def ErrorNoWorse (better worse : ObservationSurface) : Prop :=
  better.measurements = worse.measurements ∧
  better.predictionError ≤ worse.predictionError

theorem error_no_worse_refl (o : ObservationSurface) :
    ErrorNoWorse o o := by
  exact ⟨rfl, Nat.le_refl _⟩

theorem error_no_worse_trans
    {a b c : ObservationSurface}
    (hab : ErrorNoWorse a b)
    (hbc : ErrorNoWorse b c) :
    ErrorNoWorse a c := by
  exact ⟨hab.1.trans hbc.1, Nat.le_trans hab.2 hbc.2⟩

theorem strict_lower_error_implies_no_worse
    {better worse : ObservationSurface}
    (h : StrictlyLowerError better worse) :
    ErrorNoWorse better worse :=
  ⟨h.1, Nat.le_of_lt h.2⟩

theorem strict_observation_no_worse_than_loose :
    ErrorNoWorse strictObservationSurface looseObservationSurface :=
  strict_lower_error_implies_no_worse strict_observation_has_lower_error

theorem observation_error_order_witness :
    ErrorNoWorse strictObservationSurface strictObservationSurface ∧
    ErrorNoWorse strictObservationSurface looseObservationSurface :=
  ⟨error_no_worse_refl strictObservationSurface,
    strict_observation_no_worse_than_loose⟩

/-! ## Next exploration

The Comte finite-error chain is closed at preorder level. The next
honest extension would require a real empirical loss model rather than
additional arithmetic packaging.
-/

end ComteObservationErrorOrder
end Gnosis
