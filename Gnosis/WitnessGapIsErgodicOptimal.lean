import Init

namespace WitnessGapIsErgodicOptimal

def witnessGap (ergodicity : Nat) : Nat :=
  ergodicity * 3

theorem ergodic_optimal (ergodicity : Nat) :
  witnessGap ergodicity ≥ ergodicity := by
  unfold witnessGap
  omega

end WitnessGapIsErgodicOptimal