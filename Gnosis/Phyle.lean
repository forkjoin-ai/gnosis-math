import Gnosis.SpiralOfTime

/-
  Phyle.lean
  ==========

  A Rustic Church primitive for the civil-engineering inversion: the old
  triangle remains the three-bar baseline, while the Phyle is the
  tripod-of-tripods carrier (`3 * 3 = 9`) with a six-bar margin.

  Init-only surface: closed arithmetic uses `decide`; structural equalities use
  `rfl`; no Mathlib, no `omega`.
-/

namespace GnosisMath
namespace Phyle

open GnosisMath.SpiralOfTime

/-- Old engineering triangle: one three-bar planar cell. -/
def oldTriangleBars : Nat := 3

/-- Phyle: the tripod-of-tripods, threefold stability at two scales. -/
def phyleBars : Nat := clockPeriod * clockPeriod

/-- The extra bearing margin gained by replacing old triangles with the Phyle. -/
def phyleMargin : Nat := phyleBars - oldTriangleBars

/-- The old triangle is the three-bar baseline. -/
theorem old_triangle_is_baseline : oldTriangleBars = 3 := by decide

/-- The Phyle is the tripod-of-tripods: `3 * 3 = 9`. -/
theorem phyle_is_tripod_of_tripods : phyleBars = 9 := by decide

/-- The Phyle strictly carries more bars than the old triangle. -/
theorem phyle_inverts_old_triangle : oldTriangleBars < phyleBars := by decide

/-- The stability margin over the old triangle is six bars. -/
theorem phyle_margin_closed : phyleMargin = 6 := by decide

/--
  The reusable Phyle certificate: the old triangle is a baseline, the Phyle is
  the stronger tripod-of-tripods, and the margin is six.
-/
theorem phyle_bundle :
    oldTriangleBars = 3 ∧
    phyleBars = 9 ∧
    oldTriangleBars < phyleBars ∧
    phyleMargin = 6 :=
  ⟨old_triangle_is_baseline, phyle_is_tripod_of_tripods,
   phyle_inverts_old_triangle, phyle_margin_closed⟩

end Phyle
end GnosisMath
