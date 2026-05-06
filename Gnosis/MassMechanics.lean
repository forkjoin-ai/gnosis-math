import Init
import Gnosis.GodFormula

namespace Gnosis
namespace MassMechanics

open Gnosis (godWeight godWeight_antitone godWeight_ceiling godWeight_floor)

/-!
# Mass mechanics (noise -> condensation -> fixed structure)

This module formalizes the "mass mechanics" reading as a small algebra:

- `vent` = rejection/noise channel,
- `mass` = retained structural weight (`godWeight`),
- fixed points = zero-variation states.

It is intentionally discrete (`Nat`, `Int`-free) and Init-only.
-/

/-- Unsigned difference on `Nat` (distance from equality). -/
def variation (x y : Nat) : Nat :=
  if _ : x ≤ y then y - x else x - y

theorem variation_self (x : Nat) : variation x x = 0 := by
  unfold variation
  simp

/-- Structural mass at budget `R` and vent/noise `v`. -/
def mass (R v : Nat) : Nat :=
  godWeight R v

/-- More vent/noise implies weakly smaller retained mass. -/
theorem mass_antitone_in_noise (R vLo vHi : Nat)
    (hLo : vLo ≤ R) (hHi : vHi ≤ R) (h : vLo ≤ vHi) :
    mass R vHi ≤ mass R vLo :=
  godWeight_antitone R vLo vHi hLo hHi h

/-- Cooling/condensation law:
if the noise channel drops from `vHi` to `vLo`, retained mass rises (weakly). -/
theorem cooling_increases_mass (R vLo vHi : Nat)
    (hLo : vLo ≤ R) (hHi : vHi ≤ R) (h : vLo ≤ vHi) :
    mass R vLo ≥ mass R vHi := by
  exact mass_antitone_in_noise R vLo vHi hLo hHi h

/-- Endpoints of the phase line: zero noise gives ceiling mass. -/
theorem mass_ceiling_at_zero_noise (R : Nat) : mass R 0 = R + 1 :=
  godWeight_ceiling R

/-- Full noise at budget gives floor mass. -/
theorem mass_floor_at_full_noise (R : Nat) : mass R R = 1 :=
  godWeight_floor R

/-- A discrete dynamical system over capital/stock-like state. -/
def Transition := Nat → Nat

/-- Fixed point: one-step update leaves the state unchanged. -/
def IsFixedPoint (F : Transition) (k : Nat) : Prop := F k = k

/-- One-step leak/variation of the state under update map `F`. -/
def stepVariation (F : Transition) (k : Nat) : Nat := variation (F k) k

/-- Fixed points have zero one-step variation. -/
theorem fixed_point_has_zero_variation (F : Transition) (k : Nat)
    (h : IsFixedPoint F k) : stepVariation F k = 0 := by
  unfold stepVariation
  rw [h]
  exact variation_self k

/-- Solow-style discrete update (minimal algebraic scaffold):
`k_{t+1} = k_t + s*k_t - d*k_t`. -/
def solowStep (s d k : Nat) : Nat :=
  k + s * k - d * k

/-- Balanced expansion/contraction (`s = d`) implies a fixed state in one step. -/
theorem solow_balanced_is_fixed (s k : Nat) :
    solowStep s s k = k := by
  unfold solowStep
  rw [Nat.add_sub_cancel]

/-- Therefore the balanced Solow step has zero variation (condensed steady state). -/
theorem solow_balanced_zero_variation (s k : Nat) :
    variation (solowStep s s k) k = 0 := by
  rw [solow_balanced_is_fixed]
  exact variation_self k

/-- If vent/noise is frozen at `v`, mass is time-invariant across steps. -/
theorem mass_invariant_under_fixed_noise (R v : Nat) :
    mass R v = mass R v := rfl

end MassMechanics
end Gnosis
