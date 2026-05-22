import Init
import Gnosis.GodFormula
import Gnosis.VectorMath

namespace Gnosis
open Gnosis.VectorMath

/-!
# Color Theory - Formalization of Human Vision and Spectral Power

Formalizes the mathematical structures of electromagnetic radiation and
human vision within the Rustic Church (Init-only) style.

## Coverage

1. **Signals**: Light as spectral power distribution (SPD) over wavelengths.
2. **Integration**: Accumulation of spectral power across the visible spectrum.
3. **Observer Models**: CIE standard observer functions (x_bar, y_bar, z_bar).
4. **Vector Spaces**: Color representation in XYZ and opponent-color spaces.
5. **Linear Transformations**: Matrices for color space conversion.
6. **Physical Constraints**: Non-negativity of physical spectral power.
7. **Gamuts**: Bounded subsets of realizable color space.
-/

/-- Wavelength in nanometers (Nat). -/
abbrev Wavelength := Nat

/-- Visible spectrum bounds (CIE standard: 380nm to 750nm). -/
def visible_min : Wavelength := 380
def visible_max : Wavelength := 750

/-- Spectral Power Distribution (SPD): mapping wavelength to intensity (Int). -/
def SPD := Wavelength → Int

/-- CIE Standard Observer color-matching functions mapping wavelengths to tristimulus weights. -/
structure ColorMatchingFunctions where
  x_bar : Wavelength → Int
  y_bar : Wavelength → Int
  z_bar : Wavelength → Int

/-- Tristimulus coordinates (XYZ) represented as a Vector3. -/
def Tristimulus := Vector3

/-- Discrete integration (summation) over a wavelength range.
    Uses a recursive helper to accumulate spectral power. -/
def integrate_spectral (s : SPD) (m : Wavelength → Int) (start : Wavelength) (count : Nat) : Int :=
  match count with
  | 0 => s start * m start
  | n + 1 => (s (start + n + 1) * m (start + n + 1)) + integrate_spectral s m start n

/-- Compute Tristimulus values (XYZ) from an SPD using CIE functions. -/
def compute_xyz (s : SPD) (cie : ColorMatchingFunctions) : Tristimulus :=
  let range := visible_max - visible_min
  ⟨integrate_spectral s cie.x_bar visible_min range,
   integrate_spectral s cie.y_bar visible_min range,
   integrate_spectral s cie.z_bar visible_min range⟩

/-- Matrix transformation for color space conversion. -/
structure ColorMatrix where
  row1 : Vector3
  row2 : Vector3
  row3 : Vector3

/-- Apply a ColorMatrix to a Tristimulus vector. -/
def apply_color_matrix (m : ColorMatrix) (v : Tristimulus) : Tristimulus :=
  ⟨dot m.row1 v,
   dot m.row2 v,
   dot m.row3 v⟩

/-- Opponent Process Theory: Transform XYZ to (L, RG, BY).
    L: Achromatic (Luminance)
    RG: Red-Green opponent
    BY: Blue-Yellow opponent -/
def xyz_to_opponent (v : Tristimulus) : Vector3 :=
  -- Representative linear transformation:
  -- L  = Y
  -- RG = X - Y
  -- BY = Y - Z
  ⟨v.y,
   v.x - v.y,
   v.y - v.z⟩

/-- Physicality Constraint: Spectral power must be non-negative for physical light. -/
def is_physically_realizable (s : SPD) : Prop :=
  ∀ w : Wavelength, 0 ≤ s w

/-- Gamut representation: A color is in-gamut if its tristimulus values
    are non-negative and bounded by the device's primary limits. -/
def in_gamut (v : Tristimulus) (limits : Tristimulus) : Prop :=
  0 ≤ v.x ∧ v.x ≤ limits.x ∧
  0 ≤ v.y ∧ v.y ≤ limits.y ∧
  0 ≤ v.z ∧ v.z ≤ limits.z

/-- Preservation of Luminosity: A transformation preserves luminosity if
    the Y-coordinate of the output matches the Y-coordinate of the input. -/
def preserves_luminosity (m : ColorMatrix) : Prop :=
  ∀ v : Tristimulus, (apply_color_matrix m v).y = v.y

/-- Theorem: If the second row of the matrix is (0, 1, 0), it preserves luminosity.
    Proof follows from the definition of dot product and Vector3 structure. -/
theorem luminosity_preservation_by_y_row (m : ColorMatrix)
    (h_row2 : m.row2 = ⟨0, 1, 0⟩) :
    preserves_luminosity m := by
  intro v
  unfold apply_color_matrix dot
  rw [h_row2]
  show (0 : Int) * v.x + (1 : Int) * v.y + (0 : Int) * v.z = v.y
  rw [Int.zero_mul, Int.zero_mul, Int.one_mul, Int.zero_add, Int.add_zero]

/-- Convexity of Gamut (Abstract): If two colors are in gamut, their midpoint
    (representative of additive mixing) is also in gamut. -/
theorem gamut_midpoint_convexity (v1 v2 limits : Tristimulus)
    (h1 : in_gamut v1 limits) (h2 : in_gamut v2 limits) :
    in_gamut ⟨(v1.x + v2.x) / 2, (v1.y + v2.y) / 2, (v1.z + v2.z) / 2⟩ limits := by
  unfold in_gamut at *
  -- Proof of bounds for the midpoint.
  -- Each component i satisfies 0 ≤ (v1.i + v2.i) / 2 ≤ limits.i
  -- since 0 ≤ v1.i, v2.i and v1.i, v2.i ≤ limits.i.
  constructor
  · apply Int.ediv_nonneg
    · exact Int.add_nonneg h1.1 h2.1
    · decide
  constructor
  · -- (v1.x + v2.x) / 2 ≤ limits.x
    -- limits.x * 2 ≥ v1.x + v2.x
    have hx : v1.x + v2.x ≤ limits.x + limits.x := Int.add_le_add h1.2.1 h2.2.1
    rw [← Int.two_mul, Int.mul_comm] at hx
    exact Int.ediv_le_of_le_mul (by decide) hx
  constructor
  · apply Int.ediv_nonneg
    · exact Int.add_nonneg h1.2.2.1 h2.2.2.1
    · decide
  constructor
  · have hy : v1.y + v2.y ≤ limits.y + limits.y := Int.add_le_add h1.2.2.2.1 h2.2.2.2.1
    rw [← Int.two_mul, Int.mul_comm] at hy
    exact Int.ediv_le_of_le_mul (by decide) hy
  constructor
  · apply Int.ediv_nonneg
    · exact Int.add_nonneg h1.2.2.2.2.1 h2.2.2.2.2.1
    · decide
  · have hz : v1.z + v2.z ≤ limits.z + limits.z := Int.add_le_add h1.2.2.2.2.2 h2.2.2.2.2.2
    rw [← Int.two_mul, Int.mul_comm] at hz
    exact Int.ediv_le_of_le_mul (by decide) hz

end Gnosis
