/-
  IribarrenNumber.lean
  ====================

  Formalizes the Iribarren number (Surf Similarity Parameter) for wave
  breaking on slopes. 
  ξ = tan(α) / sqrt(H/L)

  In Gnosis, we model this as a "Wave Breaking Witness", proving that
  the breaking mode depends monotonically on the slope.

  Style: Rustic Church (Init-only).
-/

import Init

namespace Gnosis.Civil

/-- 
  Wave Parameters.
  slope: Tangent of the beach slope.
  height: Wave height.
  length: Wave length.
-/
structure WaveParams where
  slope : Nat
  height : Nat
  length : Nat

/-- 
  Simplified Discrete Iribarren Witness:
  ξ_sq = (slope^2 * length) / height
-/
def IribarrenSq (w : WaveParams) : Nat :=
  if w.height = 0 then 0
  else (w.slope * w.slope * w.length) / w.height

/-- 
  Theorem: Slope Monotonicity Witness.
  Increasing the slope increases the Iribarren witness squared.
-/
theorem slope_monotonicity (w : WaveParams) (s_new : Nat)
  (h_slope : s_new ≥ w.slope)
  (h_height : w.height > 0) :
  IribarrenSq ⟨s_new, w.height, w.length⟩ ≥ IribarrenSq w := by
  unfold IribarrenSq
  match w with
  | ⟨s, h, l⟩ =>
    simp only
    have h_ne : h ≠ 0 := Nat.ne_of_gt h_height
    rw [if_neg h_ne, if_neg h_ne]
    apply Nat.div_le_div_right
    apply Nat.mul_le_mul_right
    apply Nat.mul_le_mul h_slope h_slope

end Gnosis.Civil
