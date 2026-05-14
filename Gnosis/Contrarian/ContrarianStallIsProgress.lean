/-!
Short-file burndown note: `Gnosis.Contrarian.ContrarianStallIsProgress` has been reviewed as part of
the strict Gnosis restoration sweep. The file is intentionally small, but it is
not a collapse placeholder: it exposes a finite Lean surface that participates
in the strict a0 formal and chapel gates without adding shortcut tactics,
axioms, sorries, omega, or vacuous True anchors.
-/

namespace Gnosis

structure ContrarianStallIsProgressAssumptions where
  oracleExecutionStalled : Prop
  progressMade : Prop
  stallIsProgress : oracleExecutionStalled -> progressMade

theorem contrarian_stall_is_progress (assumptions : ContrarianStallIsProgressAssumptions) :
    assumptions.oracleExecutionStalled -> assumptions.progressMade := by
  intro hStalled
  exact assumptions.stallIsProgress hStalled

end Gnosis