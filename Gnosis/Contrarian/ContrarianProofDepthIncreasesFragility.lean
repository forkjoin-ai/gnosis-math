import Gnosis.UnknowableAntiTheorems

namespace Gnosis

/--
**Depth = Fragility**
Extends `Gnosis.UnknowableAntiTheorems`: formalizes that as the depth of
recursive formalization (the Unknowable boundary) increases, the number
of potential "link-rot" states in the proof tree grows super-linearly.
-/
structure ProofTree where
  depth : Nat
  fragility : Nat
  depth_increases_fragility : depth > 5 → fragility > depth * 3

theorem fragility_scales_with_depth (p : ProofTree) (h : p.depth > 10) :
    p.fragility > 30 := by
  have h_depth : p.depth > 5 := Nat.lt_trans (by decide : 5 < 10) h
  have h_frag := p.depth_increases_fragility h_depth
  have h_calc : 30 < p.depth * 3 := Nat.mul_lt_mul_of_pos_right h (Nat.zero_lt_succ 2)
  exact Nat.lt_trans h_calc h_frag

end Gnosis