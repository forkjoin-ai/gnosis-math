import Init
import Gnosis.GodFormula
import Gnosis.MassMechanics
import Gnosis.OLGModel
import Gnosis.AkerlofLemons
import Gnosis.HotellingModel

namespace Gnosis
namespace CondensationBridges

open Gnosis (godWeight)

/-!
# Condensation bridges

Cross-module bridge layer:

- OLG relay steps as condensation invariants (`t -> t+1`),
- Akerlof collapse as mass-floor identity,
- Hotelling center profile as zero-vent condensation hook.
-/

/-! ## OLG -> MassMechanics bridge -/

/-- One-step relay weight at time index `t` with growth increment `n`. -/
def relayStepWeight (R n t : Nat) : Nat :=
  godWeight (R + (t + 1) * n) (R + t * n)

theorem relay_step_weight_closed_form (R n t : Nat) :
    relayStepWeight R n t = n + 1 := by
  unfold relayStepWeight godWeight
  have hmul : (t + 1) * n = t * n + n := by
    exact Nat.succ_mul t n
  have hle : R + t * n ≤ R + (t + 1) * n := by
    calc
      R + t * n ≤ R + (t * n + n) := Nat.add_le_add_left (Nat.le_add_right (t * n) n) R
      _ = R + (t + 1) * n := by rw [hmul]
  have hmin : min (R + t * n) (R + (t + 1) * n) = R + t * n := Nat.min_eq_left hle
  rw [hmin]
  rw [hmul]
  have hshape : R + (t * n + n) = (R + t * n) + n := by
    simp [Nat.add_assoc]
  rw [hshape]
  rw [Nat.add_comm (R + t * n) n]
  rw [Nat.add_sub_cancel_right n (R + t * n)]

/-- Condensation invariant over relay time: each step has the same retained mass. -/
theorem relay_step_condensation_invariant (R n t : Nat) :
    relayStepWeight R n (t + 1) = relayStepWeight R n t := by
  rw [relay_step_weight_closed_form, relay_step_weight_closed_form]

/-- Therefore inter-step variation is zero along the relay chain. -/
theorem relay_step_variation_zero (R n t : Nat) :
    MassMechanics.variation (relayStepWeight R n (t + 1)) (relayStepWeight R n t) = 0 := by
  rw [relay_step_condensation_invariant]
  exact MassMechanics.variation_self (relayStepWeight R n t)

/-! ## Akerlof -> MassMechanics bridge -/

theorem peach_market_floor_equals_mass_floor (R : Nat) :
    AkerlofLemons.peachMarketWeight R false = MassMechanics.mass R R := by
  unfold AkerlofLemons.peachMarketWeight MassMechanics.mass
  simp

theorem lemons_witness_collapse_equals_mass_floor :
    AkerlofLemons.peachMarketWeight 10
      (AkerlofLemons.peachMarketActive AkerlofLemons.witnessVals 4 1)
      = MassMechanics.mass 10 10 := by
  rw [AkerlofLemons.witness_collapse]
  unfold MassMechanics.mass
  exact Gnosis.godWeight_floor 10

theorem certified_signal_restores_mass_ceiling (R : Nat) :
    AkerlofLemons.peachMarketWeight R true = MassMechanics.mass R 0 := by
  unfold MassMechanics.mass
  rw [AkerlofLemons.certified_signal_lifts_peach_market_weight]

theorem certified_signal_strictly_lifts_from_collapse (R : Nat) :
    AkerlofLemons.peachMarketWeight R true ≥ AkerlofLemons.peachMarketWeight R false := by
  exact AkerlofLemons.certified_signal_weight_ge_floor R

theorem certified_signal_strictly_lifts_from_collapse_of_pos (R : Nat) (hR : 0 < R) :
    AkerlofLemons.peachMarketWeight R true > AkerlofLemons.peachMarketWeight R false := by
  exact AkerlofLemons.certified_signal_weight_gt_floor_of_pos R hR

theorem signal_vs_no_signal_variation (R : Nat) :
    MassMechanics.variation
      (AkerlofLemons.peachMarketWeight R true)
      (AkerlofLemons.peachMarketWeight R false)
      = R := by
  unfold AkerlofLemons.peachMarketWeight MassMechanics.variation
  rw [Gnosis.godWeight_ceiling, Gnosis.godWeight_floor]
  cases R <;> simp

/-! ## Hotelling -> MassMechanics bridge -/

/-- At the center witness, zero unmet demand implies zero vent surrogate. -/
def hotellingCenterVentSurrogate : Nat :=
  5 - HotellingModel.leftDemand4 2 2

theorem hotelling_center_vent_zero : hotellingCenterVentSurrogate = 0 := by
  unfold hotellingCenterVentSurrogate
  simp [HotellingModel.center_left_demand4_full]

theorem hotelling_center_condensed_mass (R : Nat) :
    MassMechanics.mass R hotellingCenterVentSurrogate = R + 1 := by
  unfold MassMechanics.mass
  rw [hotelling_center_vent_zero]
  exact Gnosis.godWeight_ceiling R

end CondensationBridges
end Gnosis
