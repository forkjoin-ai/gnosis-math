import Init

/-
  UnitHydrograph.lean
  ===================

  Formalizes the Unit Hydrograph principle in hydrology.
  The runoff from multiple rainfall events is the linear superposition
  of the individual unit hydrograph responses.

  This module proves the "Linearity Witness": doubling the excess rainfall
  intensity results in doubling the discharge at all time steps.

  Style: Rustic Church (Init-only).
-/


namespace Gnosis.Civil

/-- 
  A Hydrograph as a discrete sequence of discharge values.
-/
def Hydrograph := Nat → Nat

/-- 
  Linear Scaling:
  Runoff Q(t) for rainfall intensity P is P * U(t).
-/
def ScaledRunoff (p : Nat) (u : Hydrograph) : Hydrograph :=
  λ t => p * u t

/-- 
  Superposition:
  Total runoff for two simultaneous rainfall events is the sum.
-/
def SuperposedRunoff (u1 u2 : Hydrograph) : Hydrograph :=
  λ t => u1 t + u2 t

/-- 
  Theorem: Linearity of Scaling.
  Doubling the rainfall doubles the runoff witness.
-/
theorem runoff_scaling_witness (p : Nat) (u : Hydrograph) :
  ScaledRunoff (2 * p) u = (λ t => 2 * ScaledRunoff p u t) := by
  unfold ScaledRunoff
  funext t
  rw [Nat.mul_assoc]

/-- 
  Theorem: Additivity of Response.
  The runoff from a sum of rainfall intensities is the sum of
  the individual runoffs.
-/
theorem runoff_additivity_witness (p1 p2 : Nat) (u : Hydrograph) :
  ScaledRunoff (p1 + p2) u = (λ t => ScaledRunoff p1 u t + ScaledRunoff p2 u t) := by
  unfold ScaledRunoff
  funext t
  rw [Nat.add_mul]

end Gnosis.Civil
