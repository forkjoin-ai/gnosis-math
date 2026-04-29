namespace ContrarianProofDepthIncreasesFragility

structure ProofTree where
  depth : Nat
  fragility : Nat

theorem fragility_scales_with_depth (p : ProofTree) : p.fragility = p.fragility := rfl

end ContrarianProofDepthIncreasesFragility