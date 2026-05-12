/-
  OstwaldRipening.lean
  ====================

  Formalizes the Ostwald Ripening Rate Lemma.
  Larger particles grow at the expense of smaller ones because the
  solubility of a particle increases with its curvature (Gibbs-Thomson).

  In Gnosis, we model this as a "Growth Witness" driven by the difference
  between a particle's radius and the critical radius (R*).

  Style: Rustic Church (Init-only).
-/

import Init

namespace Gnosis.Materials

/-- 
  The Growth Rate Witness (dR/dt).
  v ∝ (1/R*) - (1/R)
  r: Particle Radius
  critical_r: Critical Radius
-/
def GrowthRate (r : Nat) (critical_r : Nat) : Int :=
  if r = 0 then 0
  else if critical_r = 0 then 0
  else ((r : Int) - (critical_r : Int))

/-- 
  Theorem: Critical Radius Stability.
  A particle at the critical radius has a zero growth rate witness.
-/
theorem critical_radius_stability (r : Nat) (h_pos : r > 0) :
  GrowthRate r r = 0 := by
  unfold GrowthRate
  rw [if_neg (Nat.ne_of_gt h_pos)]
  rw [if_neg (Nat.ne_of_gt h_pos)]
  apply Int.sub_self

/-- 
  Theorem: Large Particle Growth.
  A particle larger than the critical radius has a positive growth witness.
-/
theorem large_particle_growth (r cr : Nat)
  (h_r : r > cr) (h_cr : cr > 0) :
  GrowthRate r cr > 0 := by
  unfold GrowthRate
  have h_r_pos : r > 0 := Nat.lt_trans h_cr h_r
  rw [if_neg (Nat.ne_of_gt h_r_pos)]
  rw [if_neg (Nat.ne_of_gt h_cr)]
  apply Int.sub_pos_of_lt
  apply Int.ofNat_lt.mpr h_r

end Gnosis.Materials