namespace Gnosis

structure ProofDepthFragility where
  depth : Nat
  density : Nat

theorem contrarian_proof_depth_bypass (p : ProofDepthFragility) : p.depth = p.depth := rfl

end Gnosis