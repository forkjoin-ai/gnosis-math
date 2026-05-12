/-
  MorisonEquation.lean
  ====================

  Formalizes the Morison Equation for wave forces on slender cylinders.
  The total force (F) is the sum of an inertia component (F_i) and
  a drag component (F_d):
  F = F_i + F_d

  In Gnosis, we model this as a "Decomposition Witness". Stability
  of offshore structures depends on both acceleration-dependent
  and velocity-dependent forces.

  Style: Rustic Church (Init-only).
-/

import Init

namespace Gnosis.Civil

/-- 
  Wave Kinematics Witness.
  v: Local fluid velocity.
  a: Local fluid acceleration.
-/
structure WaveKinematics where
  v : Int
  a : Int

/-- 
  Force Components.
-/
structure MorisonCoefficients where
  cm : Nat -- Inertia coefficient
  cd : Nat -- Drag coefficient

/-- 
  The Morison Force Witness (F):
  Calculates force per unit length.
  F = Cm * a + Cd * |v| * v
-/
def morison_force (c : MorisonCoefficients) (k : WaveKinematics) : Int :=
  (c.cm : Int) * (k.a : Int) + (c.cd : Int) * (if k.v ≥ 0 then k.v * k.v else - (k.v * k.v))

/-- 
  Theorem: Inertia Dominance.
  If the fluid velocity is zero, the force witness is purely inertial.
-/
theorem zero_velocity_inertial_force (c : MorisonCoefficients) (a : Int) :
  morison_force c ⟨0, a⟩ = (c.cm : Int) * a := by
  unfold morison_force
  -- if 0 >= 0 is true
  have h0 : (0 : Int) ≥ 0 := Int.le_refl 0
  rw [if_pos h0]
  -- (cm * a) + (cd * 0 * 0) = (cm * a)
  rw [Int.mul_zero, Int.mul_zero, Int.add_zero]

/-- 
  Theorem: Stationary fluid witness.
  If both velocity and acceleration are zero, the wave force must be zero.
-/
theorem stationary_fluid_no_force (c : MorisonCoefficients) :
  morison_force c ⟨0, 0⟩ = 0 := by
  rw [zero_velocity_inertial_force]
  rw [Int.mul_zero]

end Gnosis.Civil