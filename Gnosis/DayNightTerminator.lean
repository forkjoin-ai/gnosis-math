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

end DayNightTerminator
end Gnosis
