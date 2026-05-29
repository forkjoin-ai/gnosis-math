import Init
import Gnosis.AckermannFunction
import Gnosis.AckermannRuntimeCertificate
import Gnosis.AckermannLightConeBridge
import Gnosis.AckermannMonotone

/-
  FrontierComputability.lean
  ==========================

  Feeds the now-PROVEN universality (`AckermannMonotone.eventual_domination`)
  back into the light-cone geometry. Where the bridge's NP co-theorem used a
  single decided witness, this module proves the GENERAL statement:

      every fixed primitive-recursive ladder level is EVENTUALLY subluminal —
      strictly inside the light cone, never reaching the luminal Ackermann
      front, never entering the spacelike (time-travel / super-primitive-recursive)
      region.

  This is the rigorous form of "tractable computation can't catch the photon",
  now backed by the full domination theorem rather than a calibration point.

  Init + the bridge + the monotonicity tower. Zero `sorry`, zero new `axiom`.
-/

namespace FrontierComputability

open AckermannFunction
open AckermannUniversality
open AckermannRuntimeCertificate
open Gnosis.CausalDiamond
open AckermannLightConeBridge

/-- The fixed-level-`k` runtime `n ↦ hyperop k n n`. For each fixed `k` this is
    a primitive-recursive function — a single rung of the hyperoperation
    ladder (`k = 1` addition, `k = 2` multiplication, `k = 3` exponentiation,
    …). -/
def levelRuntime (k : Nat) : Runtime := fun n => hyperop k n n

/-- **Fixed PR levels are eventually subluminal.** For `n ≥ k + 3` the level-`k`
    runtime sits STRICTLY inside the light cone (negative interval, timelike):
    it never reaches the luminal Ackermann front the photon rides. The proven
    form of the NP co-theorem. -/
theorem fixed_level_eventually_subluminal (k n : Nat) (hn : k + 3 ≤ n) :
    intervalSquared origin (runtimeEvent (levelRuntime k) n) < 0 := by
  apply subluminal_is_strictly_timelike
  show hyperop k n n < ackermannCeiling n
  exact AckermannMonotone.eventual_domination k n hn

/-- A fixed PR level is eventually 100%-certified below the ceiling at each
    such input — strictly, not just `≤`. -/
theorem fixed_level_strictly_below_ceiling (k n : Nat) (hn : k + 3 ≤ n) :
    levelRuntime k n < ackermannCeiling n :=
  AckermannMonotone.eventual_domination k n hn

/-- **Fixed PR levels never time-travel.** A level-`k` runtime is never in the
    spacelike (super-Ackermann / super-primitive-recursive) region for `n ≥ k + 3`: it
    cannot send information into its own past. -/
theorem fixed_level_never_time_travel (k n : Nat) (hn : k + 3 ≤ n) :
    ¬ (ackermannCeiling n < levelRuntime k n) := by
  intro h
  have hlt : hyperop k n n < ackermannCeiling n :=
    AckermannMonotone.eventual_domination k n hn
  simp only [levelRuntime] at h
  omega

/-- **The frontier is strict.** No fixed PR level is the Ackermann diagonal:
    for `n ≥ k + 3`, `hyperop k n n ≠ A(n)`. The diagonal genuinely escapes the
    ladder — the luminal front is not attained by any rung. -/
theorem diagonal_escapes_every_level (k n : Nat) (hn : k + 3 ≤ n) :
    hyperop k n n ≠ ackermannDiag n := by
  have hlt : hyperop k n n < ackermannDiag n :=
    AckermannMonotone.eventual_domination k n hn
  omega

/-- **Polynomial time is eventually strictly subluminal.** A polynomial runtime
    `n ↦ n^d` is bounded by the exponential level (`n^d ≤ n^n = hyperop 3 n n`)
    and so falls strictly below the Ackermann ceiling for `n ≥ max(d, 6)`. The
    entire polynomial hierarchy is forever sub-frontier — it never catches the
    photon. -/
theorem polynomial_eventually_subluminal (d n : Nat) (hn : 6 ≤ n) (hd : d ≤ n) :
    n ^ d < ackermannDiag n := by
  have h1 : n ^ d ≤ n ^ n := Nat.pow_le_pow_right (by omega) hd
  have h2 : n ^ n = hyperop 3 n n := (hyperop_three n n).symm
  have h3 : hyperop 3 n n < ackermannDiag n :=
    AckermannMonotone.eventual_domination 3 n (by omega)
  omega

/-- The geometric face: a polynomial runtime is strictly timelike (inside the
    light cone) for `n ≥ max(d, 6)`. -/
theorem polynomial_strictly_timelike (d n : Nat) (hn : 6 ≤ n) (hd : d ≤ n) :
    intervalSquared origin (runtimeEvent (fun m => m ^ d) n) < 0 := by
  apply subluminal_is_strictly_timelike
  show n ^ d < ackermannCeiling n
  exact polynomial_eventually_subluminal d n hn hd

end FrontierComputability
