import Gnosis.ImmigrationTopology

namespace Gnosis

/-!
# THM-DIVERSITY-is-CONCURRENCY

In the restored Init-only transport-growth layer, diversity and concurrency are
the same count read through two interfaces.
-/

theorem diversity_is_concurrency_exact (beta1 : Nat) :
    diversityCount beta1 = effectiveConcurrency beta1 := by
  exact diversity_is_concurrency beta1

theorem immigration_preserves_the_identity (host : HostTopology) (imm : ImmigrantTopology) :
    diversityCount (postImmigrationPaths host imm) =
      effectiveConcurrency (postImmigrationPaths host imm) := by
  exact diversity_is_concurrency _

theorem immigration_strictly_grows_both_when_positive
    (host : HostTopology) (imm : ImmigrantTopology)
    (hImm : 0 < imm.knot.beta1) :
    diversityCount host.knot.beta1 < diversityCount (postImmigrationPaths host imm) ∧
      effectiveConcurrency host.knot.beta1 <
        effectiveConcurrency (postImmigrationPaths host imm) := by
  constructor
  · unfold diversityCount postImmigrationPaths
    omega
  · exact immigration_grows_concurrency host imm hImm

end Gnosis
