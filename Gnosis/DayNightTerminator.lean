namespace Gnosis
namespace DayNightTerminator

/-!
# Day/Night Terminator — the lit/dark split on a sphere

Spec for the monster-studio Earth day/night lighting
(`apps/monster-studio/src/scene/earth-scene.ts`). A surface point with outward
normal `n` is LIT by a sun in direction `s` exactly when the sun is above its
local horizon — i.e. `dot(n, s) > 0`. The TERMINATOR (the day/night boundary)
is the great circle `dot(n, s) = 0`: the intersection of the sphere with the
plane through the centre perpendicular to the sun direction.

Init-only (no Mathlib): integer vectors. The sign facts are proved by `omega`
(trichotomy on the integer dot product) and witnessed by `decide` at concrete
sun directions. Continuous claims (the lit set is exactly a hemisphere) are
witnessed, not proved over the reals.
-/

structure V3 where
  x : Int
  y : Int
  z : Int
deriving DecidableEq, Repr

def V3.neg (v : V3) : V3 := ⟨-v.x, -v.y, -v.z⟩
def V3.dot (a b : V3) : Int := a.x * b.x + a.y * b.y + a.z * b.z

/-- LIT: the sun is above the point's horizon. -/
def lit (n s : V3) : Prop := 0 < V3.dot n s
/-- On the day/night boundary (sun exactly on the horizon). -/
def onTerminator (n s : V3) : Prop := V3.dot n s = 0

instance (n s : V3) : Decidable (lit n s) := by unfold lit; infer_instance
instance (n s : V3) : Decidable (onTerminator n s) := by unfold onTerminator; infer_instance

/-- The terminator is exactly the `dot = 0` set (definitional). -/
theorem terminator_iff (n s : V3) : onTerminator n s ↔ V3.dot n s = 0 := Iff.rfl

/-- Dot is linear under negating the normal: `dot(-n, s) = -dot(n, s)`. The
antipodal point sees the opposite illumination sign. -/
theorem dot_neg_left (n s : V3) : V3.dot (V3.neg n) s = - V3.dot n s := by
  simp only [V3.dot, V3.neg, Int.neg_mul]
  omega

/-- **Trichotomy**: every point is lit, on the terminator, or in the dark — the
sphere splits cleanly into day, the terminator circle, and night. -/
theorem day_terminator_night (n s : V3) :
    lit n s ∨ onTerminator n s ∨ V3.dot n s < 0 := by
  unfold lit onTerminator
  omega

/-- **Antipodal complement**: off the terminator, a point is lit iff its
antipode is dark. (Day and night are exact opposites across the globe.) -/
theorem antipode_opposite (n s : V3) (h : V3.dot n s ≠ 0) :
    lit n s ↔ ¬ lit (V3.neg n) s := by
  unfold lit
  rw [dot_neg_left]
  omega

/-- The terminator is symmetric: a point is on it iff its antipode is. -/
theorem terminator_antipodal (n s : V3) :
    onTerminator n s ↔ onTerminator (V3.neg n) s := by
  unfold onTerminator
  rw [dot_neg_left]
  omega

/-! ## Shadow predicate and sun-flip antisymmetry -/

/-- IN SHADOW: the sun is below the point's horizon. -/
def shadow (n s : V3) : Prop := V3.dot n s < 0

instance (n s : V3) : Decidable (shadow n s) := by unfold shadow; infer_instance

/-- **Full trichotomy with the shadow state.** Every point is lit, on the
terminator, or in shadow — and exactly one holds (the three are mutually
exclusive by the integer trichotomy). -/
theorem lit_terminator_shadow (n s : V3) :
    lit n s ∨ onTerminator n s ∨ shadow n s := by
  unfold lit onTerminator shadow
  omega

/-- Lit and shadow are mutually exclusive. -/
theorem lit_not_shadow (n s : V3) : lit n s → ¬ shadow n s := by
  unfold lit shadow; omega

/-- Dot is linear under negating the **sun**: `dot(n, -s) = -dot(n, s)`. -/
theorem dot_neg_sun (n s : V3) : V3.dot n (V3.neg s) = - V3.dot n s := by
  simp only [V3.dot, V3.neg, Int.mul_neg]
  omega

/-- **Antisymmetry of illumination under a sun flip.** Moving the sun to the
antipode (a 12-hour rotation) turns a lit point into a shadowed one. -/
theorem flip_sun_lit_to_shadow (n s : V3) (h : lit n s) : shadow n (V3.neg s) := by
  unfold lit shadow at *
  have := dot_neg_sun n s
  omega

/-- …and a shadowed point becomes lit. Day and night swap exactly under a sun
flip. -/
theorem flip_sun_shadow_to_lit (n s : V3) (h : shadow n s) : lit n (V3.neg s) := by
  unfold lit shadow at *
  have := dot_neg_sun n s
  omega

/-- The terminator great circle is **invariant** under flipping the sun — the
same boundary separates the two hemispheres regardless of which faces the sun. -/
theorem terminator_sun_flip_invariant (n s : V3) :
    onTerminator n s ↔ onTerminator n (V3.neg s) := by
  unfold onTerminator
  have := dot_neg_sun n s
  omega

/-! ## The sub-solar point is maximally lit -/

/-- The squared length of a direction is non-negative (`dot v v ≥ 0`). -/
theorem dot_self_nonneg (v : V3) : 0 ≤ V3.dot v v := by
  have nn : ∀ a : Int, 0 ≤ a * a := by
    intro a
    rcases Int.le_total 0 a with h | h
    · exact Int.mul_nonneg h h
    · have e : a * a = (-a) * (-a) := by rw [Int.neg_mul, Int.mul_neg, Int.neg_neg]
      rw [e]; exact Int.mul_nonneg (by omega) (by omega)
  unfold V3.dot
  have := nn v.x; have := nn v.y; have := nn v.z
  omega

/-- The **sub-solar point** (normal equal to a nonzero sun direction) is lit:
its illumination is the squared sun length, which is strictly positive. -/
theorem subsolar_lit (s : V3) (h : V3.dot s s ≠ 0) : lit s s := by
  unfold lit
  have := dot_self_nonneg s
  omega

/-- Per-coordinate AM–GM: `2·x·y ≤ x² + y²`, init-only from `0 ≤ (x−y)²`. -/
theorem amgm (x y : Int) : 2 * (x * y) ≤ x * x + y * y := by
  have hsq : 0 ≤ (x - y) * (x - y) := by
    rcases Int.le_total 0 (x - y) with h | h
    · exact Int.mul_nonneg h h
    · have e : (x - y) * (x - y) = (-(x - y)) * (-(x - y)) := by
        rw [Int.neg_mul, Int.mul_neg, Int.neg_neg]
      rw [e]; exact Int.mul_nonneg (by omega) (by omega)
  have expand : (x - y) * (x - y) = x * x - 2 * (x * y) + y * y := by
    rw [Int.sub_mul, Int.mul_sub, Int.mul_sub, Int.mul_comm y x]; omega
  omega

/-- **Sub-solar point is maximally lit (Cauchy–Schwarz at equal norm).** For a
normal `n` on the same sphere as the sun (`dot n n = dot s s`, the unit-sphere
constraint, supplied as a hypothesis since this model is over `Int`), no point
is brighter than the sub-solar point: `dot n s ≤ dot s s`. Proof: sum the three
per-coordinate AM–GM bounds `2·nᵢ·sᵢ ≤ nᵢ² + sᵢ²` to get `2·(n·s) ≤ n·n + s·s
= 2·(s·s)`. -/
theorem subsolar_maximal (n s : V3) (h : V3.dot n n = V3.dot s s) :
    V3.dot n s ≤ V3.dot s s := by
  have ax := amgm n.x s.x
  have ay := amgm n.y s.y
  have az := amgm n.z s.z
  unfold V3.dot at *
  omega

/-! ## Witnesses (decide) — concrete sun directions -/

-- Sun toward +X: the +X point is lit, −X is dark, the YZ great circle is the
-- terminator.
example : lit ⟨1, 0, 0⟩ ⟨1, 0, 0⟩ := by decide
example : ¬ lit ⟨-1, 0, 0⟩ ⟨1, 0, 0⟩ := by decide
example : onTerminator ⟨0, 1, 0⟩ ⟨1, 0, 0⟩ := by decide
example : onTerminator ⟨0, 0, 1⟩ ⟨1, 0, 0⟩ := by decide

-- Oblique sun (2,1,3): the subsolar point is lit (dot = 14), its antipode dark,
-- and a perpendicular point (3,0,-2) is on the terminator (6 + 0 − 6 = 0).
example : lit ⟨2, 1, 3⟩ ⟨2, 1, 3⟩ := by decide
example : ¬ lit ⟨-2, -1, -3⟩ ⟨2, 1, 3⟩ := by decide
example : onTerminator ⟨3, 0, -2⟩ ⟨2, 1, 3⟩ := by decide

-- Shadow + sun-flip witnesses.
example : shadow ⟨-1, 0, 0⟩ ⟨1, 0, 0⟩ := by decide        -- midnight is in shadow
example : shadow ⟨1, 0, 0⟩ (V3.neg ⟨1, 0, 0⟩) := by decide  -- flipping the sun shadows noon

end DayNightTerminator
end Gnosis
