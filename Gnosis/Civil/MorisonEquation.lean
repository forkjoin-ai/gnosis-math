import Init

/-
  MorisonEquation.lean
  ====================

  Formalizes the Morison equation for hydrodynamic forces on offshore
  structures. The force (F) is the sum of inertia and drag components.

  In Gnosis, we model this as a "Hydrodynamic Force Witness", proving that
  the total force is zero if both acceleration and velocity are zero.

  Style: Rustic Church (Init-only).
-/


namespace Gnosis.Civil

/-- 
  Hydrodynamic Parameters.
  cm: Inertia coefficient.
  cd: Drag coefficient.
-/
structure HydrodynamicParams where
  cm : Nat
  cd : Nat

/-- 
  Force Witness:
  F = cm * acceleration + cd * velocity_squared
-/
def MorisonForce (p : HydrodynamicParams) (a v_sq : Nat) : Nat :=
  p.cm * a + p.cd * v_sq

/-- 
  Theorem: Static Equilibrium Witness.
  If both acceleration and velocity squared are zero, the force is zero.
-/
theorem static_force_zero (p : HydrodynamicParams) :
  MorisonForce p 0 0 = 0 := by
  unfold MorisonForce
  rw [Nat.mul_zero, Nat.mul_zero, Nat.add_zero]

end Gnosis.Civil
