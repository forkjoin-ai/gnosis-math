/-
  CommerceGravity.lean
  ====================

  The Huff / gravity model that the cave's commerce corridors use to quantify
  "audience distance and pull". A resident at distance `d` from a business of
  attractiveness `A` feels an UN-NORMALIZED pull

      u(A, d)  ∝  A / d^β        (here β = 2, the classic Huff exponent)

  and patronizes business `b` with probability `u_b / Σ_j u_j`. The renderer
  routes homes to the businesses they are pulled to; pull is the audience-weighted
  sum of these probabilities. To make the model legible we must KNOW it behaves:

      * MORE attractive  ⇒  strictly more pull   (at fixed distance)
      * FARTHER away      ⇒  strictly less pull   (at fixed attractiveness)

  We avoid real division (Init-only, no Mathlib) by comparing pulls via
  CROSS-MULTIPLICATION, which is exact over the integers:

      A₁ / d₁²  <  A₂ / d₂²    ⟺    A₁ · d₂²  <  A₂ · d₁²

  `pullLt A₁ d₁ A₂ d₂` is exactly that integer relation. Distances are positive
  integers (scaled metres), attractiveness a positive integer (scaled). The two
  monotonicity theorems below are proved by `omega`/`nlinarith`-free integer
  reasoning, so the runtime `huffPull` (apps/monster-studio/src/lib/commerce-gravity.ts)
  rests on a certified core. Pull is a hospitality instance: a business is a
  high-`H` site for the resident audience.

  PROVEN (Init-only, no Mathlib):
    * pull_strict_mono_attractiveness : fixed distance, more A ⇒ strictly more pull.
    * pull_strict_anti_distance       : fixed A, more distance ⇒ strictly less pull.
    * pull_mono_attractiveness        : non-strict version (≤).
  WITNESSED (decide): concrete pull comparisons.
-/

namespace Gnosis
namespace CommerceGravity

/-- A positive (scaled) distance: at least 1 so the gravity kernel never divides
    by zero. -/
def PosDist (d : Int) : Prop := 1 ≤ d

/-- A positive (scaled) attractiveness. -/
def PosAttr (a : Int) : Prop := 1 ≤ a

/-- Cross-multiplied pull comparison: `A₁/d₁² < A₂/d₂²` over the integers, i.e.
    the resident is MORE pulled to the second business than the first. Exact —
    no division, no rounding. -/
def pullLt (a1 d1 a2 d2 : Int) : Prop := a1 * (d2 * d2) < a2 * (d1 * d1)

/-- Non-strict pull comparison. -/
def pullLe (a1 d1 a2 d2 : Int) : Prop := a1 * (d2 * d2) ≤ a2 * (d1 * d1)

/-- A positive distance squared is positive (used to keep the cross-multiply
    direction). -/
theorem distSq_pos (d : Int) (hd : PosDist d) : 0 < d * d := by
  unfold PosDist at hd
  have h0 : (0 : Int) < d := by omega
  exact Int.mul_pos h0 h0

/-- MONOTONE in attractiveness: at a FIXED distance `d`, a strictly more
    attractive business exerts strictly more pull. (Classic Huff: bigger store,
    more draw.) -/
theorem pull_strict_mono_attractiveness
    (a1 a2 d : Int) (hd : PosDist d) (ha : a1 < a2) :
    pullLt a1 d a2 d := by
  unfold pullLt
  have hpos : 0 < d * d := distSq_pos d hd
  -- a1 * (d*d) < a2 * (d*d) since a1 < a2 and d*d > 0.
  exact Int.mul_lt_mul_of_pos_right ha hpos

/-- Non-strict monotone in attractiveness (≤). -/
theorem pull_mono_attractiveness
    (a1 a2 d : Int) (hd : PosDist d) (ha : a1 ≤ a2) :
    pullLe a1 d a2 d := by
  unfold pullLe
  have hpos : 0 < d * d := distSq_pos d hd
  exact Int.mul_le_mul_of_nonneg_right ha (Int.le_of_lt hpos)

/-- ANTI-MONOTONE in distance: at a FIXED attractiveness `a`, a business that is
    strictly FARTHER away exerts strictly LESS pull. The near business (distance
    `d1`) beats the far one (`d2`, `d1 < d2`). (Friction of distance.) -/
theorem pull_strict_anti_distance
    (a d1 d2 : Int) (ha : PosAttr a) (hd1 : PosDist d1) (hd2 : PosDist d2)
    (hd : d1 < d2) :
    pullLt a d2 a d1 := by
  -- Goal after unfold: a * (d1*d1) < a * (d2*d2), i.e. the FAR business (first
  -- argument d2) is less pulled than the NEAR business (d1).
  unfold pullLt
  have hapos : 0 < a := by unfold PosAttr at ha; omega
  -- 0 < d1, 0 < d2, and d1 < d2 with both positive ⇒ d1*d1 < d2*d2.
  have h1 : (0 : Int) < d1 := by unfold PosDist at hd1; omega
  have h2 : (0 : Int) < d2 := by unfold PosDist at hd2; omega
  have hsq : d1 * d1 < d2 * d2 := by
    have hle : d1 * d1 ≤ d1 * d2 := Int.mul_le_mul_of_nonneg_left (Int.le_of_lt hd) (Int.le_of_lt h1)
    have hlt : d1 * d2 < d2 * d2 := Int.mul_lt_mul_of_pos_right hd h2
    exact Int.lt_of_le_of_lt hle hlt
  -- a > 0 and d1*d1 < d2*d2 ⇒ a*(d1*d1) < a*(d2*d2).
  exact Int.mul_lt_mul_of_pos_left hsq hapos

/-- Concrete witness: a 2× attractive store at the same distance wins. -/
example : pullLt 1 3 2 3 := by unfold pullLt; decide

/-- Concrete witness: at equal attractiveness, the nearer store (d=2) beats the
    farther (d=5): `pullLt a d_far a d_near`. -/
example : pullLt 4 5 4 2 := by unfold pullLt; decide

end CommerceGravity
end Gnosis
