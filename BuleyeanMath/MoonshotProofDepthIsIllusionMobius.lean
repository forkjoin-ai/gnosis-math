namespace BuleyeanMath

structure MobiusProofDepth where
  apparent_depth : Nat
  mobius_limit : Nat
  folds_back : apparent_depth > mobius_limit

theorem proof_depth_bounded_by_mobius (m : MobiusProofDepth) :
    m.apparent_depth > m.mobius_limit := by
  exact m.folds_back

end BuleyeanMath