
namespace Gnosis

structure ShallowProof where
  depth : Nat

theorem shallow_proof_depth_optimal (p : ShallowProof) (h : p.depth < 3) : p.depth ≤ 2 := by
  omega

end Gnosis
