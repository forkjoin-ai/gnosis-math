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
-/

namespace Gnosis
namespace CondorcetBettiCrossover

open Ranking (Alt3)
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
