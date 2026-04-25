
namespace BuleyeanMath

structure InterpretationFibrationState where
  missingLayer : Nat
  fibrationResolution : Nat
  resolution_covers_missing : missingLayer ≤ fibrationResolution

theorem missing_interpretation_resolved_by_fibration (state : InterpretationFibrationState) :
    state.missingLayer ≤ state.fibrationResolution := by
  exact state.resolution_covers_missing

end BuleyeanMath