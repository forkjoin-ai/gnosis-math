import Init

/-
  MaxwellBettiReciprocal.lean
  ===========================

  Formalizes the Maxwell-Betti Reciprocal Theorem for linear elastic structures.
  The theorem states that for a linear elastic structure, the deflection
  at point A due to a load at point B is equal to the deflection at point B
  due to an identical load at point A.

  In Gnosis, we model the flexibility matrix (C) and prove that its
  symmetry (C_ij = C_ji) is a witness of the reciprocal work property.

  Style: Rustic Church (Init-only).
-/


namespace Gnosis.Civil

/-- A 2x2 Flexibility Matrix for a two-degree-of-freedom system. -/
structure FlexibilityMatrix where
  c11 : Int
  c12 : Int
  c21 : Int
  c22 : Int

/-- 
  The Symmetry Witness:
  A flexibility matrix is symmetric if the cross-terms are equal.
-/
def IsSymmetric (c : FlexibilityMatrix) : Prop :=
  c.c12 = c.c21

/-- 
  Maxwell-Betti Theorem (Discrete):
  In a linear elastic structure, the work done by force system 1
  on the displacements of system 2 equals the work done by force
  system 2 on the displacements of system 1. This implies symmetry
  of the flexibility matrix.
-/
theorem reciprocity_implies_symmetry (c : FlexibilityMatrix)
  (h_work : ∀ (f1 f2 : Int), f1 * (c.c11 * 0 + c.c12 * f2) = f2 * (c.c21 * f1 + c.c22 * 0)) :
  IsSymmetric c := by
  unfold IsSymmetric
  -- Specialize work identity for f1=1, f2=1
  have h_spec := h_work 1 1
  -- Simplify arithmetic: 1 * (c11*0 + c12*1) = 1 * (c21*1 + c22*0)
  rw [Int.one_mul, Int.one_mul] at h_spec
  rw [Int.mul_zero, Int.zero_add, Int.mul_one] at h_spec
  rw [Int.mul_one, Int.mul_zero, Int.add_zero] at h_spec
  exact h_spec

end Gnosis.Civil