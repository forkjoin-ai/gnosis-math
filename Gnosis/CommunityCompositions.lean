import Gnosis.CommunityDominance
import Gnosis.InterferenceCoarsening

namespace Gnosis
namespace CommunityCompositions

/-!
# Community Compositions

This module restores a finite Init-compatible core for the historical community
composition sketch.  The old file contained many higher-level applications; the
stable kernel here is local-to-global aggregation of finite context and its
monotone effect on remaining burden.
-/

structure LocalCommunityPair where
  failureBurden : Nat
  contextA : Nat
  contextB : Nat

namespace LocalCommunityPair

def mergedContextLower (pair : LocalCommunityPair) : Nat :=
  max pair.contextA pair.contextB

def mergedContextUpper (pair : LocalCommunityPair) : Nat :=
  pair.contextA + pair.contextB

def remainingBurdenAt (pair : LocalCommunityPair) (context : Nat) : Nat :=
  pair.failureBurden - context

def remainingA (pair : LocalCommunityPair) : Nat :=
  pair.remainingBurdenAt pair.contextA

def remainingB (pair : LocalCommunityPair) : Nat :=
  pair.remainingBurdenAt pair.contextB

def remainingMerged (pair : LocalCommunityPair) : Nat :=
  pair.remainingBurdenAt pair.mergedContextLower

theorem merged_context_ge_left (pair : LocalCommunityPair) :
    pair.contextA ≤ pair.mergedContextLower := by
  unfold mergedContextLower
  exact Nat.le_max_left _ _

theorem merged_context_ge_right (pair : LocalCommunityPair) :
    pair.contextB ≤ pair.mergedContextLower := by
  unfold mergedContextLower
  exact Nat.le_max_right _ _

theorem merged_context_le_upper (pair : LocalCommunityPair) :
    pair.mergedContextLower ≤ pair.mergedContextUpper := by
  unfold mergedContextLower mergedContextUpper
  exact Nat.max_le.mpr ⟨Nat.le_add_right _ _, Nat.le_add_left _ _⟩

theorem remaining_monotone
    (pair : LocalCommunityPair)
    {earlier later : Nat}
    (hContext : earlier ≤ later) :
    pair.remainingBurdenAt later ≤ pair.remainingBurdenAt earlier := by
  unfold remainingBurdenAt
  exact Nat.sub_le_sub_left hContext pair.failureBurden

theorem merged_remaining_le_left (pair : LocalCommunityPair) :
    pair.remainingMerged ≤ pair.remainingA := by
  exact pair.remaining_monotone pair.merged_context_ge_left

theorem merged_remaining_le_right (pair : LocalCommunityPair) :
    pair.remainingMerged ≤ pair.remainingB := by
  exact pair.remaining_monotone pair.merged_context_ge_right

theorem merged_remaining_le_min_local (pair : LocalCommunityPair) :
    pair.remainingMerged ≤ min pair.remainingA pair.remainingB := by
  exact (Nat.le_min).mpr ⟨pair.merged_remaining_le_left, pair.merged_remaining_le_right⟩

theorem left_convergence_preserved
    (pair : LocalCommunityPair)
    (hA : pair.remainingA = 0) :
    pair.remainingMerged = 0 := by
  exact Nat.eq_zero_of_le_zero (by simpa [hA] using pair.merged_remaining_le_left)

theorem right_convergence_preserved
    (pair : LocalCommunityPair)
    (hB : pair.remainingB = 0) :
    pair.remainingMerged = 0 := by
  exact Nat.eq_zero_of_le_zero (by simpa [hB] using pair.merged_remaining_le_right)

theorem merged_interval_nonempty (pair : LocalCommunityPair) :
    pair.mergedContextLower ≤ pair.mergedContextUpper := by
  exact pair.merged_context_le_upper

def asSignedDeficit (pair : LocalCommunityPair) : Int :=
  Int.ofNat pair.remainingMerged

def afterCommunityDiscount (pair : LocalCommunityPair) : Int :=
  communityDiscount pair.asSignedDeficit

theorem community_discount_strict_on_merged (pair : LocalCommunityPair) :
    pair.afterCommunityDiscount < pair.asSignedDeficit := by
  exact community_discount_strict pair.asSignedDeficit

theorem community_discount_preserves_merged_order
    {left right : LocalCommunityPair}
    (hRemaining : left.asSignedDeficit ≤ right.asSignedDeficit) :
    left.afterCommunityDiscount ≤ right.afterCommunityDiscount := by
  exact community_discount_preserves_order hRemaining

def toCoarseningWitness
    (pair : LocalCommunityPair)
    (hSupport : 1 < pair.failureBurden -> 1 < pair.mergedContextLower)
    (hRepair : 0 < pair.failureBurden - 1) :
    InterferenceCoarsening.FiniteCoarseningWitness where
  fineInitialLive := pair.failureBurden
  coarseInitialLive := pair.mergedContextLower
  coarseTerminalLive := 1
  coarseTotalVented := 0
  coarseTotalRepairDebt := pair.failureBurden - 1
  supportPreserving := hSupport
  survivorFaithful := by
    intro _
    rfl
  zeroVentReflectsRepair := by
    intro _ _
    exact Or.inl hRepair

end LocalCommunityPair

def twoCommunitySample : LocalCommunityPair where
  failureBurden := 5
  contextA := 2
  contextB := 3

theorem two_community_sample_merge_context :
    twoCommunitySample.mergedContextLower = 3 := by
  rfl

theorem two_community_sample_remaining :
    twoCommunitySample.remainingMerged = 2 := by
  rfl

theorem two_community_sample_improves_left :
    twoCommunitySample.remainingMerged ≤ twoCommunitySample.remainingA := by
  exact twoCommunitySample.merged_remaining_le_left

theorem two_community_sample_discount_strict :
    twoCommunitySample.afterCommunityDiscount <
      twoCommunitySample.asSignedDeficit := by
  exact twoCommunitySample.community_discount_strict_on_merged

def twoCommunityCoarseningWitness :
    InterferenceCoarsening.FiniteCoarseningWitness :=
  twoCommunitySample.toCoarseningWitness
    (by
      intro _
      decide)
    (by decide)

theorem two_community_coarsening_schema :
    0 < twoCommunityCoarseningWitness.coarseTotalVented \/
      0 < twoCommunityCoarseningWitness.coarseTotalRepairDebt := by
  exact
    twoCommunityCoarseningWitness.schema_instantiated
      (by
        unfold InterferenceCoarsening.FiniteCoarseningWitness.fineContagious
        decide)
      (by
        unfold InterferenceCoarsening.FiniteCoarseningWitness.coarseDeterministicCollapse
        decide)

end CommunityCompositions
end Gnosis
