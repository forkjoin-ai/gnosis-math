import Gnosis.ImmigrationTopology

namespace Gnosis

/-!
# Community Dominance

Community support lowers the remaining signed integration burden by a fixed
unit in this simplified Init-only model.
-/

/-- A one-step community discount on signed integration burden. -/
def communityDiscount (d : Int) : Int :=
  communityReducedDeficit d

theorem community_discount_strict (d : Int) :
    communityDiscount d < d := by
  exact community_accelerates_integration d

theorem community_discount_preserves_order {d1 d2 : Int} (h : d1 ≤ d2) :
    communityDiscount d1 ≤ communityDiscount d2 := by
  unfold communityDiscount communityReducedDeficit
  exact Int.sub_le_sub_right h 1

theorem community_discount_on_assimilation (host : HostTopology) (imm : ImmigrantTopology) :
    communityDiscount (assimilationDeficit host imm) <
      assimilationDeficit host imm := by
  exact community_discount_strict _

end Gnosis
