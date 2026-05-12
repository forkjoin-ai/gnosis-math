/-
  AbramsLaw.lean
  ==============

  Formalizes Abrams's Law for concrete strength:
  S = A / B^w
  where S is the compressive strength and w is the water-cement ratio.

  In Gnosis, we model this as a "Monotonicity Witness". Increasing the
  water-cement ratio decreases the hardened strength of the concrete.

  Style: Rustic Church (Init-only).
-/

import Init

namespace Gnosis.Civil

/-- 
  Concrete Strength Model.
-/
structure ConcreteModel where
  strength_of : Nat → Nat

/-- 
  Abrams Consistency Witness:
  A valid model must show strength decreasing as WCRatio increases.
-/
def IsValidAbramsModel (m : ConcreteModel) : Prop :=
  ∀ w1 w2, w1 < w2 → m.strength_of w1 > m.strength_of w2

/-- 
  Theorem: High Water Weakness.
  In a valid Abrams model, a lower water-cement ratio always produces
   a stronger concrete witness.
-/
theorem low_wc_is_stronger (m : ConcreteModel)
  (h_abrams : IsValidAbramsModel m)
  (w1 w2 : Nat)
  (h_lower : w1 < w2) :
  m.strength_of w1 > m.strength_of w2 := by
  apply h_abrams
  exact h_lower

end Gnosis.Civil