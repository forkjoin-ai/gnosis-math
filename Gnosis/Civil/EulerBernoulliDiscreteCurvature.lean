/-
  EulerBernoulliDiscreteCurvature.lean
  ====================================

  Formalizes the discrete Euler-Bernoulli relationship for linear elastic
  beam elements. In a discrete grid of spacing Δx = 1, the curvature κ
  at node i is defined by the second-order central difference of the
  transverse displacement y.

  The bending moment M is the product of the flexural rigidity EI and
  the curvature κ. This module proves the stability witness that a linear
  displacement field (zero curvature) results in zero internal moment.

  Style: Rustic Church (Init-only).
-/

import Init

namespace Gnosis.Civil

/-- Flexural rigidity (EI) as a non-negative scalar. -/
def FlexuralRigidity := Nat

/-- 
  Discrete Curvature (κ) at node i+1 using central difference:
  κ[i+1] = y[i+2] - 2*y[i+1] + y[i]
-/
def Curvature (y : Nat → Int) (i : Nat) : Int :=
  y (i + 2) - 2 * y (i + 1) + y i

/-- 
  Bending Moment (M) at node i+1:
  M[i+1] = EI * κ[i+1]
-/
def BendingMoment (ei : FlexuralRigidity) (y : Nat → Int) (i : Nat) : Int :=
  (Int.ofNat ei) * Curvature y i

/-- 
  Theorem: Linear Displacement Yields Zero Moment.
  If the displacement field is linear (y[i] = m*i + c), then the internal
  bending moment is zero at all nodes.
-/
theorem linear_displacement_yields_zero_moment
  (m c : Int)
  (ei : FlexuralRigidity)
  (y : Nat → Int)
  (h_linear : ∀ i, y i = m * (i : Int) + c) :
  ∀ i, BendingMoment ei y i = 0 := by
  intro i
  unfold BendingMoment
  unfold Curvature
  rw [h_linear (i + 2), h_linear (i + 1), h_linear i]
  -- Resolve curvature
  have h_zero : (m * (↑(i + 2) : Int) + c) - 2 * (m * (↑(i + 1) : Int) + c) + (m * (↑i : Int) + c) = 0 := by
    rw [Int.natCast_add, Int.natCast_add]
    repeat rw [Int.mul_add]
    rw [Int.mul_comm m ↑2, Int.two_mul m, Int.mul_one]
    repeat rw [Int.two_mul]
    repeat rw [Int.sub_add]
    repeat rw [Int.sub_eq_add_neg]
    repeat rw [Int.neg_add]
    repeat rw [Int.add_assoc]
    ac_rfl
  rw [h_zero]
  apply Int.mul_zero

end Gnosis.Civil
