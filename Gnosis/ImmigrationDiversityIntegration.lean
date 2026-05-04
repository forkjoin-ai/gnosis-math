import Gnosis.CommunityDominance
import Gnosis.DiversityIsConcurrency
import Gnosis.DiversityOptimality
import Gnosis.ImmigrationTopology

namespace Gnosis

/-!
# Immigration Diversity Integration

This module closes the simple loop:

- immigration adds paths,
- more paths mean more diversity,
- diversity means more concurrency,
- assimilation removes transient overhead,
- community support lowers the remaining signed burden.
-/

theorem immigration_grows_diversity
    (host : HostTopology) (imm : ImmigrantTopology)
    (hImm : 0 < imm.knot.beta1) :
    diversityCount host.knot.beta1 <
      diversityCount (postImmigrationPaths host imm) :=
  -- Init-only: `diversityCount` is the identity on `Nat`, and
  -- `postImmigrationPaths host imm = host.knot.beta1 + imm.knot.beta1`,
  -- so the goal reduces by `rfl` to `host.knot.beta1 < host.knot.beta1 + imm.knot.beta1`,
  -- which is exactly `Nat.lt_add_of_pos_right` from the `Init` core.
  Nat.lt_add_of_pos_right hImm

theorem immigration_grows_diversity_and_concurrency
    (host : HostTopology) (imm : ImmigrantTopology)
    (hImm : 0 < imm.knot.beta1) :
    diversityCount host.knot.beta1 <
      diversityCount (postImmigrationPaths host imm) ∧
    effectiveConcurrency host.knot.beta1 <
      effectiveConcurrency (postImmigrationPaths host imm) := by
  exact immigration_strictly_grows_both_when_positive host imm hImm

theorem immigration_closes_deficit_toward_frontier
    {intrinsicBeta : Nat}
    (host : HostTopology) (imm : ImmigrantTopology)
    (hBelow : host.knot.beta1 < intrinsicBeta)
    (hStream : 1 ≤ host.knot.beta1) :
    topologicalDeficit intrinsicBeta (postImmigrationPaths host imm) ≤
      topologicalDeficit intrinsicBeta host.knot.beta1 := by
  exact immigration_closes_deficit host imm hBelow hStream

theorem assimilation_reaches_zero_signed_deficit
    (host : HostTopology) (imm : ImmigrantTopology) :
    assimilationDeficit host imm = 0 := by
  exact immigration_zero_deficit_at_match host imm

theorem community_improves_the_assimilation_boundary
    (host : HostTopology) (imm : ImmigrantTopology) :
    communityDiscount (assimilationDeficit host imm) <
      assimilationDeficit host imm := by
  exact community_discount_on_assimilation host imm

theorem greedy_rejection_fails_on_positive_crossing_immigration
    (host : HostTopology) (imm : ImmigrantTopology)
    (hImm : 0 < imm.knot.crossingNumber) :
    ¬ greedyPolicy host.knot.crossingNumber (postImmigrationKnot host imm).crossingNumber := by
  exact greedy_rejection_deadlocks host imm hImm

end Gnosis
