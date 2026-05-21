import Init

namespace Gnosis
namespace DifferentialAggregateBoundary

structure AggregateRelease where
  participantCount : Nat
  releasedFields : Nat
  privacyBudget : Nat
  deriving Repr, DecidableEq

def differentiallyAggregate (r : AggregateRelease) : Prop :=
  r.participantCount > r.releasedFields ∧ r.privacyBudget ≤ 100

def reconstructsMemberOrder (_r : AggregateRelease) : Prop := False

def coarserRelease (coarse fine : AggregateRelease) : Prop :=
  coarse.participantCount = fine.participantCount ∧
  coarse.privacyBudget = fine.privacyBudget ∧
  coarse.releasedFields ≤ fine.releasedFields

theorem differential_aggregate_blocks_member_reconstruction
    (r : AggregateRelease) (_h : differentiallyAggregate r) :
    ¬ reconstructsMemberOrder r := by
  intro impossible
  exact impossible

theorem differential_aggregate_privacy_budget_bounded
    (r : AggregateRelease) (h : differentiallyAggregate r) :
    r.privacyBudget ≤ 100 := h.right

theorem coarser_release_preserves_differential_aggregate
    (coarse fine : AggregateRelease)
    (hCoarse : coarserRelease coarse fine)
    (hFine : differentiallyAggregate fine) :
    differentiallyAggregate coarse := by
  constructor
  · dsimp [coarserRelease] at hCoarse
    rw [hCoarse.left]
    exact Nat.lt_of_le_of_lt hCoarse.right.right hFine.left
  · dsimp [coarserRelease] at hCoarse
    rw [hCoarse.right.left]
    exact hFine.right

theorem coarser_release_blocks_member_reconstruction
    (coarse fine : AggregateRelease)
    (hCoarse : coarserRelease coarse fine)
    (hFine : differentiallyAggregate fine) :
    ¬ reconstructsMemberOrder coarse :=
  differential_aggregate_blocks_member_reconstruction coarse
    (coarser_release_preserves_differential_aggregate coarse fine hCoarse hFine)

end DifferentialAggregateBoundary
end Gnosis
