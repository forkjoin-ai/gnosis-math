/-!
# Graph Cycle Rank Sketch

Init-only graph first-Betti proxy: `|E| - |V| + β₀`.
-/

namespace PlanetaryHomologySandbox

structure GraphCounts where
  vertices : Nat
  edges : Nat
  beta0 : Nat
deriving Repr, DecidableEq

def graphFirstBettiSketch (counts : GraphCounts) : Nat :=
  counts.edges - counts.vertices + counts.beta0

theorem graphFirstBettiSketch_unfold
    (counts : GraphCounts) :
    graphFirstBettiSketch counts =
      counts.edges - counts.vertices + counts.beta0 := by
  rfl

theorem tree_like_cycle_rank_zero
    (vertices : Nat) :
    graphFirstBettiSketch
      { vertices := vertices, edges := vertices, beta0 := 0 } = 0 := by
  unfold graphFirstBettiSketch
  simp

end PlanetaryHomologySandbox
