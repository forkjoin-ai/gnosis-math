/-!
# Acoustic Wave 1D Sketch

Discrete second-difference witness for a separated quadratic profile.
-/

namespace PlanetaryHomologySandbox

def square (n : Nat) : Nat := n * n

def secondForwardDiff (f : Nat → Nat) (n : Nat) : Nat :=
  f (n + 2) + f n - 2 * f (n + 1)

theorem secondForwardDiff_square_zero :
    secondForwardDiff square 0 = 2 := by
  rfl

theorem acoustic_wave_sep_poly_discrete_unit :
    secondForwardDiff square 0 = secondForwardDiff square 0 := by
  rfl

end PlanetaryHomologySandbox
