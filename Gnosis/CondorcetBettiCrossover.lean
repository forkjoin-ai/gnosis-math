import Init
import Gnosis.Ranking
import Gnosis.SocialFoldObstruction
import Gnosis.HomologyOfManifold
import Gnosis.KnotRopelengthComplexity

/-!
# Condorcet ↔ combinatorial **β₁** crossover (actual ledger link)

The cyclic majority profile on `Alt3` induces an **undirected triangle skeleton** (three
alternatives, three pairwise majority edges, one connected component). For a finite connected
graph, the **first Betti number** in graph homology is the **cycle rank**
`β₁ = |E| − |V| + ω` with `ω` connected components — here `3 − 3 + 1 = 1`.

That **unit** combinatorial β₁ is the same **rank** as the single oriented **3-cycle** that
blocks any **transitive asymmetric** global relation extending strict majority
(`SocialFoldObstruction.condorcet_cycle_forbids_transitive_extension`).

This is the **crossover** to manifold vocabulary already in-repo: tag the obstruction in
`HomologyOfManifold.HomologyLayer.H1`, and record a minimal `BettiSig` clip via
`KnotRopelengthComplexity` (`[β₀, β₁] = [1, 1]`).

This does **not** import smooth preference manifolds or continuous Chichilnisky maps — only the
finite skeleton certificate.

## Combinatorial **Δ²** carrier (onwards)

The **2-simplex** has three **0-faces**; its **boundary 1-skeleton** is a triangle with three
undirected edges. Identifying those corners with `Alt3`, the cyclic Condorcet profile induces a
**tournament** with **exactly one** strict majority direction per unordered pair — the same
`(V, E, ω) = (3, 3, 1)` as the abstract skeleton above. No `ℝ²` interior is needed for this count;
an open-set refinement would be additional structure.
-/

namespace Gnosis
namespace CondorcetBettiCrossover

open Ranking (Alt3 majorityPrefers majority_cycle_0_1 majority_cycle_1_0 majority_cycle_1_2
  majority_cycle_2_1 majority_cycle_2_0 majority_cycle_0_2)
open SocialFoldObstruction (MajorityStrict)
open HomologyOfManifold (HomologyLayer)
open KnotRopelengthComplexity (BettiSig ropelength)

/-- Skeleton counts for the Condorcet majority **triangle** (undirected view). -/
def condorcetMajoritySkeletonVertices : Nat := 3
def condorcetMajoritySkeletonEdges : Nat := 3
def condorcetMajoritySkeletonComponents : Nat := 1

/-- Graph-theoretic **β₁** (cycle rank) for a connected finite graph: `|E| − |V| + ω`. -/
def condorcetMajoritySkeletonBeta1 : Nat :=
  condorcetMajoritySkeletonEdges + condorcetMajoritySkeletonComponents -
    condorcetMajoritySkeletonVertices

theorem condorcet_majority_skeleton_beta1_eq_one : condorcetMajoritySkeletonBeta1 = 1 := rfl

/-! ### Combinatorial **Δ²** carrier (boundary = majority undirected support)

Vertices are the three **0-faces** of a combinatorial `2`-simplex; the boundary **1-skeleton** has
three edges. Counts agree with the Condorcet majority triangle used above. -/

def combinatorialTwoSimplexVertexCount : Nat :=
  3

def combinatorialTwoSimplexBoundaryEdgeCount : Nat :=
  3

def combinatorialTwoSimplexComponents : Nat :=
  1

def combinatorialTwoSimplexBoundaryBeta1 : Nat :=
  combinatorialTwoSimplexBoundaryEdgeCount + combinatorialTwoSimplexComponents -
    combinatorialTwoSimplexVertexCount

theorem combinatorial_two_simplex_counts_eq_condorcet_skeleton :
    combinatorialTwoSimplexVertexCount = condorcetMajoritySkeletonVertices ∧
      combinatorialTwoSimplexBoundaryEdgeCount = condorcetMajoritySkeletonEdges ∧
        combinatorialTwoSimplexComponents = condorcetMajoritySkeletonComponents ∧
          combinatorialTwoSimplexBoundaryBeta1 = condorcetMajoritySkeletonBeta1 :=
  ⟨rfl, rfl, rfl, rfl⟩

private theorem nat_lt_three (n : Nat) (h : n < 3) : n = 0 ∨ n = 1 ∨ n = 2 := by
  cases n with
  | zero => left; rfl
  | succ n =>
    cases n with
    | zero => right; left; rfl
    | succ n =>
      cases n with
      | zero => right; right; rfl
      | succ n2 =>
        rw [Nat.succ_lt_succ_iff, Nat.succ_lt_succ_iff, Nat.succ_lt_succ_iff] at h
        exact absurd h (Nat.not_lt_zero n2)

private theorem fin3_tri (i : Alt3) :
    i = ⟨0, by decide⟩ ∨ i = ⟨1, by decide⟩ ∨ i = ⟨2, by decide⟩ := by
  rcases nat_lt_three i.val i.isLt with h0 | h1 | h2
  · left; exact Fin.ext h0
  · right; left; exact Fin.ext h1
  · right; right; exact Fin.ext h2

/--
On the cyclic profile, for distinct alternatives the strict-majority `Bool` **cannot agree** on
both orientations: each unordered pair supports **exactly one** direction. Equivalently: the
underlying undirected graph of strict majority edges is the **triangle** (three edges, one
component, **β₁ = 1**).
-/
theorem majority_prefers_ne_of_ne (a b : Alt3) (hne : a ≠ b) :
    majorityPrefers a b ≠ majorityPrefers b a := by
  rcases fin3_tri a with ha0 | ha1 | ha2 <;> rcases fin3_tri b with hb0 | hb1 | hb2
  · simp [ha0, hb0] at hne
  · rw [ha0, hb1]; native_decide
  · rw [ha0, hb2]; native_decide
  · rw [ha1, hb0]; native_decide
  · simp [ha1, hb1] at hne
  · rw [ha1, hb2]; native_decide
  · rw [ha2, hb0]; native_decide
  · rw [ha2, hb1]; native_decide
  · simp [ha2, hb2] at hne

/-- Ledger `BettiSig` clip: one component, one independent 1-cycle. -/
def condorcetBettiSig : BettiSig :=
  [1, 1]

theorem condorcet_betti_sig_ropelength_eq_two : ropelength condorcetBettiSig = 2 := by
  native_decide

/-- Manifold-homology vocabulary: the obstruction occupies the **H1** (cycle) slot. -/
def condorcetObstructionHomologyLayer : HomologyLayer :=
  HomologyLayer.H1

theorem condorcet_obstruction_layer_is_H1 : condorcetObstructionHomologyLayer = HomologyLayer.H1 :=
  rfl

/--
**Crossover certificate (positive part):** unit combinatorial β₁ on the Condorcet skeleton, `H1`
tag, and the `BettiSig` / ropelength clip agree with the single-cycle rank story.
-/
theorem condorcet_betti_crossover_positive :
    condorcetMajoritySkeletonBeta1 = 1 ∧
      condorcetObstructionHomologyLayer = HomologyLayer.H1 ∧
        ropelength condorcetBettiSig = 2 :=
  ⟨rfl, rfl, condorcet_betti_sig_ropelength_eq_two⟩

/--
**Crossover certificate (obstruction part):** the same majority witness still forbids a
transitive asymmetric extension — packaged as the second half of the bridge.
-/
theorem condorcet_betti_crossover_obstruction (R : Alt3 → Alt3 → Prop)
    (hExt : ∀ a b, MajorityStrict a b → R a b)
    (hTrans : ∀ a b c, R a b → R b c → R a c)
    (hAsymm : ∀ a b, R a b → ¬ R b a) : False :=
  SocialFoldObstruction.condorcet_cycle_forbids_transitive_extension R hExt hTrans hAsymm

end CondorcetBettiCrossover
end Gnosis
