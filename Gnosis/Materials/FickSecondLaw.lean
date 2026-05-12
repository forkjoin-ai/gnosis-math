/-
  FickSecondLaw.lean
  ==================

  Formalizes a discrete interpretation of Fick's Second Law:
  ∂c/∂t = D ∂²c/∂x²

  In Gnosis, we model the rate of concentration change (Accumulation)
  as a witness of the spatial curvature of the concentration field.
  Stability is reached when the spatial curvature is zero (Linear profile).

  Style: Rustic Church (Init-only).
-/

import Init

namespace Gnosis.Materials

/-- 
  Concentration Profile across discrete nodes.
-/
def ConcentrationProfile := Nat → Int

/-- 
  Spatial Curvature (Second difference) at node i+1.
-/
def SpatialCurvature (c : ConcentrationProfile) (i : Nat) : Int :=
  c (i + 2) - 2 * c (i + 1) + c i

/-- 
  Accumulation Witness:
  The change in concentration per unit time.
-/
def Accumulation (d : Int) (c : ConcentrationProfile) (i : Nat) : Int :=
  d * SpatialCurvature c i

/-- 
  Theorem: Steady State Witness.
  In a linear concentration profile (c_i = m*i + k), the accumulation
  witness is zero everywhere (Steady state).
-/
theorem steady_state_linear_profile (d m k : Int) (c : ConcentrationProfile)
  (h_linear : ∀ i, c i = m * i + k) :
  ∀ i, Accumulation d c i = 0 := by
  intro i
  unfold Accumulation
  unfold SpatialCurvature
  rw [h_linear (i + 2), h_linear (i + 1), h_linear i]
  -- Resolve: (m*(i+2) + k) - 2*(m*(i+1) + k) + (m*i + k) = 0
  have h_zero : (m * (i + 2 : Nat) + k) - 2 * (m * (i + 1 : Nat) + k) + (m * (i : Nat) + k) = 0 := by
    rw [Int.mul_add, Int.mul_add]
    rw [Int.two_mul (m * (i + 1 : Nat) + k)]
    rw [Int.mul_comm m 2]
    match m * (i : Nat), m, k with
    | mi, mv, kv =>
      show mi + mv * 2 + kv - (mi + mv + kv + (mi + mv + kv)) + (mi + kv) = 0
      rw [Int.mul_comm mv 2, Int.two_mul mv]
      repeat rw [Int.sub_add]
      ac_rfl
  rw [h_zero]
  apply Int.mul_zero

end Gnosis.Materials