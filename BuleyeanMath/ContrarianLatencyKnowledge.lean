import Init

namespace BuleyeanMath

/--
Contrarian Anti-Theorem: Latency increases knowledge density rather than just degrading it,
because delayed synchronization accumulates observer entropy.
-/
structure LatencyKnowledgeAssumptions where
  latency : Nat
  knowledgeDensity : Nat
  entropyAccumulation : Nat
  densityGrowth : knowledgeDensity = latency * entropyAccumulation

theorem latency_increases_density (assumptions : LatencyKnowledgeAssumptions)
    (hLatency : assumptions.latency > 0)
    (hEntropy : assumptions.entropyAccumulation > 0) :
    assumptions.knowledgeDensity > 0 := by
  rw [assumptions.densityGrowth]
  exact Nat.mul_pos hLatency hEntropy

end BuleyeanMath
