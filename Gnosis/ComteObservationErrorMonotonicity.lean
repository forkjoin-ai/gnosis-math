import Gnosis.ComtePositiveEmpirics

/-
  ComteObservationErrorMonotonicity.lean
  ======================================

  Burns down the next-exploration target from
  `ComtePositiveEmpirics`: lower prediction error is the stricter
  finite positive-stage certificate.

  Imports `Gnosis.ComtePositiveEmpirics`. Zero `sorry`, zero new
  `axiom`.
-/

namespace Gnosis
namespace ComteObservationErrorMonotonicity

open ComtePositiveEmpirics
open BuleyErgodicClosure
open SkyrmsUltraLongRunEquilibrium

def looseObservationSurface : ObservationSurface :=
  { measurements := 3
    predictionError := 2
    closureWitness := skyrms_ulr_is_bulk_novikov_closed }

def strictObservationSurface : ObservationSurface :=
  { measurements := 3
    predictionError := 0
    closureWitness := skyrms_ulr_is_bulk_novikov_closed }

/-- Lower prediction error at equal measurement count is stricter. -/
def StrictlyLowerError (better worse : ObservationSurface) : Prop :=
  better.measurements = worse.measurements ∧
  better.predictionError < worse.predictionError

theorem strict_observation_has_lower_error :
    StrictlyLowerError strictObservationSurface looseObservationSurface := by
  unfold StrictlyLowerError strictObservationSurface looseObservationSurface
  decide

theorem strict_observation_is_auditable :
    Auditable strictObservationSurface := by
  unfold Auditable strictObservationSurface
  exact ⟨by decide, rfl⟩

theorem loose_observation_not_auditable :
    ¬ Auditable looseObservationSurface := by
  intro h
  have hErr : looseObservationSurface.predictionError = 0 := h.2
  exact (by decide : ¬ (2 : Nat) = 0) hErr

theorem lower_error_surface_is_stricter_positive_certificate :
    StrictlyLowerError strictObservationSurface looseObservationSurface ∧
    Auditable strictObservationSurface ∧
    ¬ Auditable looseObservationSurface := by
  exact ⟨strict_observation_has_lower_error,
    strict_observation_is_auditable,
    loose_observation_not_auditable⟩

/-! ## Next exploration

Closed by `Gnosis.ComteObservationErrorOrder`: the concrete
strict/loose pair now feeds a reusable finite observation preorder.
-/

end ComteObservationErrorMonotonicity
end Gnosis
