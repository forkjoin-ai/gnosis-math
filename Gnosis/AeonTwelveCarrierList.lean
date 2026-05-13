import Init
import Gnosis.GodFormula
import Gnosis.AeonCyclicPluckerLabels
import Gnosis.AeonStandingWaveCoordinateBridge
import Gnosis.AeonCycleTwelveShadow

namespace Gnosis
namespace AeonTwelveCarrierList

/-!
# Aeon-12 **carrier list** (ordered track toward gcd / Plücker / God-band / orbit toys)

This module **sequences** the discrete certificates that feed heavier
“carrier” storylines (`gcd` stride period, column-clock ⇄ `cyclicSucc`, God-formula
slices at `R = 12`, and pair dynamics linked to the **6** chord classes).

**Convention (stride):** one tick advances every column index by **`+s (mod 12)`** on
`Fin 12`, realized as **`iteratedCyclicSucc` composition**
`iteratedCyclicSucc h12 s` per tick (val-level: add **`s`** once per tick).

So **`k` ticks** move **`(x.val + k * s) % 12`**, i.e. **`iteratedCyclicSucc h12 (k * s)`**.

The **return time** certificate below uses **`m = (12 / gcd(12,s)) · s`**: it is *a*
modulus killing the origin — not a claim that smaller positive multiples never return for
other vertices (`Fin 12` iteration story stays in `AeonCycleTwelveShadow`).
-/

open AmplituhedronAttention.Grassmannian
open Gnosis.DiscreteClosedTimelikeStep
open Gnosis.AeonCycleTwelveShadow
open Gnosis.AeonStandingWaveCoordinateBridge

theorem twelve_dvd_mul_div_cancel_mul {g a : Nat} (_hg0 : 0 < g) (hgL : g ∣ twelve) (hgR : g ∣ a) :
    twelve ∣ (twelve / g) * a := by
  rcases hgR with ⟨k, rfl⟩
  rw [← Nat.mul_assoc]
  rw [Nat.mul_comm (twelve / g) g]
  rw [Nat.mul_div_cancel' hgL]
  exact Nat.dvd_mul_right twelve k

theorem twelve_dvd_mul_div_gcd_mul_s (s : Nat) : twelve ∣ (twelve / Nat.gcd twelve s) * s :=
  twelve_dvd_mul_div_cancel_mul
    (Nat.pos_of_ne_zero (Nat.gcd_ne_zero_left (m := twelve) (n := s) (Nat.succ_ne_zero 11)))
    (Nat.gcd_dvd_left twelve s)
    (Nat.gcd_dvd_right twelve s)

/-- First list item: return at the origin for stride exponent built from gcd and twelve. -/
theorem stride_origin_return (s : Nat) :
    iteratedCyclicSucc h12 ((twelve / Nat.gcd twelve s) * s) finZero = finZero :=
  (iterate_zero_fixed_iff_dvd _).2 (twelve_dvd_mul_div_gcd_mul_s s)

/-- Plücker label step: `rotateIndex` matches `cyclicSucc` on `Fin 12` (see lemmas below). -/

theorem rotateIndex_eq_cyclicSucc_val {j : Nat} (hj : j < twelve) :
    AeonCyclicPluckerLabels.rotateIndex j = (cyclicSucc h12 ⟨j, hj⟩).val := by
  simp [AeonCyclicPluckerLabels.rotateIndex, AeonCyclicPluckerLabels.ambientDim, cyclicSucc,
    twelve_eq_aeon]

theorem rotatePluckerLabel_axis_pair :
    AeonCyclicPluckerLabels.rotatePluckerLabel [0, 1] = [1, 2] := by
  native_decide

/-- Per-chart Plücker move on the coordinate plane: `[1,2]` minor vanishes after one column tick. -/
theorem aeon_plucker_one_step_not_principal :
    pluckerCoord aeonBasisCoordinatePlane [1, 2] = 0 := by
  native_decide

/-- God formula slice: phase in Fin twelve with vent below thirteen for conservation lemmas below. -/
structure GodTwelveSlice where
  phase : Fin twelve
  vent : Fin 13

theorem god_twelve_slice_conservation (s : GodTwelveSlice) (hv : s.vent.val ≤ twelve) :
    godWeight twelve s.vent.val + s.vent.val = twelve + 1 :=
  godWeight_conservation twelve s.vent.val hv

/-- `v = 0` vent at **`R = 12`**: maximal weight **13** on the God-formula slice. -/
theorem god_twelve_top_vent_eq_thirteen : godWeight twelve 0 = 13 := by
  native_decide

/-- Rotate ordered pair endpoints by plus-one mod twelve, then re-sort; compares to circChordAux_rot. -/
def rotPairNat (p : Nat × Nat) : Nat × Nat :=
  let i := (p.1 + 1) % twelve
  let j := (p.2 + 1) % twelve
  if _ : i < j then (i, j) else (j, i)

theorem shortChord_rotPairNat_eq (p : Nat × Nat) (hp : p ∈ pairsIJ) :
    shortChord (rotPairNat p) = shortChord p := by
  revert p hp
  native_decide

theorem shortChord_attains_six_values :
    (∃ p ∈ pairsIJ, shortChord p = 1) ∧
      (∃ p ∈ pairsIJ, shortChord p = 2) ∧
        (∃ p ∈ pairsIJ, shortChord p = 3) ∧
          (∃ p ∈ pairsIJ, shortChord p = 4) ∧
            (∃ p ∈ pairsIJ, shortChord p = 5) ∧
              (∃ p ∈ pairsIJ, shortChord p = 6) := by
  native_decide

/-- Burnside-style pointer: six cardinality lemmas on pairsIJ live in AeonCycleTwelveShadow. -/

end AeonTwelveCarrierList
end Gnosis
