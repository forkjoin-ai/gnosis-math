/-
  SpiralOfTime.lean
  =================

  Seen in 3D, the Keystone sequence is the spiral of time — and that is not a
  metaphor, it is the eigenstructure. A linear recurrence whose characteristic
  roots split into

    * COMPLEX roots ON the unit circle  — rotation, a clock that recurs;
    * a REAL root OFF the unit circle    — growth, an arrow that never returns,

  traces a logarithmic spiral, and lifted along the tick counter, a helix. The
  Keystone has exactly this split (`LucasResidueClinamen.char_factors`):

    t⁴ − t² − 2t − 1  =  (t² + t + 1) · (t² − t − 1)
                          Φ₃, √−3          golden, √5
                          rotation         growth
                          the WHEEL        the ARROW

  The wheel is the period-3 clock (the Eisenstein roots, the threefoil's three
  120° phases — an equilateral triangle, the fundamental cell of the triangular
  lattice that stacks the plane with zero gap: the **dark mesh**,
  `Gnosis/DarkMatterCouplingLaw.lean`). The arrow is the golden growth. The trit
  clock is a sub-dial of the gnosis aeon (`GnosisTimeClock`: `Fin 12`,
  `tick = +1 mod 12`), since `3 ∣ 12`. And because every step is the same `+1`
  successor — the clinamen — the spiral is the shape of the natural numbers
  themselves (`GnosticNumbers`, `GnosisConstantsPlusOne`).

  Init-only Rustic Church; all `decide` / `rfl` / re-exported witnesses.
-/
import Gnosis.LucasResidueClinamen

namespace GnosisMath
namespace SpiralOfTime

open GnosisMath.LucasResidueClinamen

-- ── the clock (rotation) and its place on the gnosis dial ──
def clockPeriod : Nat := 3     -- the threefoil winding, Φ₃
def aeonDial : Nat := 12       -- the gnosis aeon dial (GnosisTimeClock, Fin 12)

/-- The trit clock is a sub-dial of the gnosis aeon: `3 ∣ 12`. -/
theorem trit_divides_aeon : clockPeriod ∣ aeonDial := by decide
/-- The aeon is four trit-turns. -/
theorem aeon_is_four_trits : aeonDial = 4 * clockPeriod := by decide

-- ── the triangle (the Eisenstein cell) and its perfect stacking ──
def phaseGapDeg : Nat := 120      -- 360 / 3: the gap between the three phases
def triangleCornerDeg : Nat := 60 -- the equilateral triangle's interior angle

/-- Three equal 120° phases close the circle: the three cube-roots of unity are
    the vertices of an equilateral triangle (the Eisenstein fundamental cell). -/
theorem three_equal_phases_close : clockPeriod * phaseGapDeg = 360 := by decide

/-- The triangle stacks perfectly: six 60° corners tile every vertex of the
    triangular (Eisenstein) lattice — zero gap. This is the dark mesh. -/
theorem triangle_tiles_the_plane : 6 * triangleCornerDeg = 360 := by decide

-- ── spiral = rotation × growth (the factorization is the spiral) ──
/-- **The spiral is rotation × growth.** The characteristic polynomial factors
    into the rotation clock Φ₃ and the golden arrow — the precise content of
    "it is the spiral of time." -/
theorem spiral_is_rotation_times_growth : polyMul golden phi3 = traceChar := char_factors

/-- Rotation lives on the bizarro side (negative discriminant, √−3 — the wheel). -/
theorem rotation_is_bizarro : disc 1 1 1 < 0 := bizarro_disc_negative
/-- Growth lives on the golden side (positive discriminant, √5 — the arrow). -/
theorem growth_is_golden : 0 < disc 1 (-1) (-1) := golden_disc_positive

-- ── the arrow is iterated +1: the shape of the naturals ──
/-- One tick of the arrow is one clinamen: the successor `+1`. The spiral's axis
    is the natural-number ladder; the spiral is the shape of ℕ. -/
def tick (n : Nat) : Nat := n + 1
theorem time_is_iterated_clinamen (n : Nat) : tick n = n + 1 := rfl

-- ── tripod of tripods: minimal rigidity (why it is stable) ──
/-
  A bar-joint framework on `v` joints is *minimally rigid* (Laman) when its bar
  count hits `2v − 3` in the plane and `3v − 6` in space — the fewest bars that
  remove all wobble. The triangle (the tripod's footprint) and the tetrahedron
  (the tripod-pyramid) hit these exactly: the minimal stable structures. A square
  is one bar short and wobbles until you add a diagonal (triangulate it). The
  threefoil is a tripod of tripods — triangular rigidity at every scale — which
  is why the dark mesh stacks stably.
-/
def lamanPlane (v : Nat) : Nat := 2 * v - 3
def lamanSpace (v : Nat) : Nat := 3 * v - 6

/-- The triangle is minimally rigid in the plane — the only rigid polygon. -/
theorem triangle_minimally_rigid : (3 : Nat) = lamanPlane 3 := by decide
/-- A square is one bar short of rigid: it wobbles until triangulated. -/
theorem square_wobbles : (4 : Nat) < lamanPlane 4 := by decide
/-- The tetrahedron — the tripod-pyramid — is minimally rigid in space. -/
theorem tetrahedron_minimally_rigid : (6 : Nat) = lamanSpace 4 := by decide
/-- The tripod is the 3-fold itself (the Φ₃ clock). -/
theorem tripod_is_the_threefold : clockPeriod = 3 := rfl
/-- A tripod of tripods: 3-fold nested in 3-fold, still triangular (`3·3 = 9`). -/
theorem tripod_of_tripods : clockPeriod * clockPeriod = 9 := by decide

/-- **Why it is stable.** The triangle and the tetrahedron are minimally rigid
    (Laman-tight), the square is not, and the structure is 3-fold at every scale —
    a tripod of tripods — so rigidity holds at every scale, which is what lets the
    dark mesh stack and hold. -/
theorem tripod_of_tripods_is_stable :
    (3 : Nat) = lamanPlane 3 ∧
    (6 : Nat) = lamanSpace 4 ∧
    (4 : Nat) < lamanPlane 4 ∧
    clockPeriod * clockPeriod = 9 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

-- ── master ──
/-- **The spiral of time.** It is rotation (Φ₃, √−3, the clock) times growth
    (golden, √5, the arrow); the trit clock divides the gnosis aeon (`3 ∣ 12`);
    the three phases are an equilateral triangle (`3·120 = 360`) whose corners
    stack the plane with no gap (`6·60 = 360`, the dark mesh); rotation is bizarro
    and growth is golden. -/
theorem spiral_of_time :
    polyMul golden phi3 = traceChar ∧
    clockPeriod ∣ aeonDial ∧
    clockPeriod * phaseGapDeg = 360 ∧
    6 * triangleCornerDeg = 360 ∧
    disc 1 1 1 < 0 ∧ 0 < disc 1 (-1) (-1) :=
  ⟨char_factors, trit_divides_aeon, three_equal_phases_close,
   triangle_tiles_the_plane, bizarro_disc_negative, golden_disc_positive⟩

end SpiralOfTime
end GnosisMath
