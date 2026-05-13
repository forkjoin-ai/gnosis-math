import Init
import Gnosis.AeonCycleTwelveShadow
import Gnosis.AeonTwelveCarrierList

namespace Gnosis
namespace AeonTwelvePairsIJZmodAction

/-!
# **`pairsIJ`** as a **`ℤ/12ℤ`**–torsor (**inverse strides**, modulus arithmetic)

**`rotPairNatAdd`** (**`Gnosis.AeonTwelveCarrierList`**) translates both chord endpoints by **`amt (mod 12)`**
and re-sorts --- on **`pairsIJ`** it aggregates **compositionally** (**`rotPairNatAdd_add_eq_rot_comp`**).

This module isolates the **additive inverse** in **`ℤ/12ℤ`** as an explicit **`Nat`** stride (**`zmodTwelveStrideInv`**),
and proves **`rotPairNatAdd`** **right–inverts** along that inverse (**`rot_pair_nat_add_stride_inverse_cancel`**).

Together with **`fin128HammingDist_symm`** (**`Gnosis.AeonTwelveHammingGrayDynamics`**) and injective slotting
(**`chordGateResolutionSlot`**), the **sorted Hamming histogram** along **`amt`** matches the histogram along the
group inverse — packaged computationally as **`chord_rot_hist_sorted_amt_eq_zmod_stride_inv`** in **`Gnosis.AeonTwelveHypercubeMajorization`**.

Zero `sorry`, zero new `axiom`.
-/

open Gnosis.AeonCycleTwelveShadow
open Gnosis.AeonTwelveCarrierList

/-- Representative of **`−[amt] ∈ ℤ/12ℤ`** used as a **`rotPairNatAdd`** stride (**`Nat`** reducer). -/
def zmodTwelveStrideInv (amt : Nat) : Nat :=
  (twelve - amt % twelve) % twelve

theorem stride_sum_mod_twelve_zero (amt : Nat) :
    (amt % twelve + zmodTwelveStrideInv amt) % twelve = 0 := by
  rcases Nat.eq_zero_or_pos (amt % twelve) with ha0 | ha_pos
  · simp [zmodTwelveStrideInv, ha0]
  · have hlt := Nat.mod_lt amt twelve_pos
    have hsub_lt : twelve - amt % twelve < twelve := Nat.sub_lt twelve_pos ha_pos
    have hs : (twelve - amt % twelve) % twelve = twelve - amt % twelve :=
      Nat.mod_eq_of_lt hsub_lt
    simp only [zmodTwelveStrideInv, hs]
    rw [Nat.add_sub_of_le (Nat.le_of_lt hlt)]
    simp

/-- **`rotPairNatAdd`** shear cancellation (**group inverse on **`pairsIJ`** gates**). -/
theorem rot_pair_nat_add_stride_inverse_cancel (amt : Nat) (p : Nat × Nat) (hp : p ∈ pairsIJ) :
    rotPairNatAdd (zmodTwelveStrideInv amt) (rotPairNatAdd amt p) = p := by
  let a := amt % twelve
  let inv := zmodTwelveStrideInv amt
  have hz : (a + inv) % twelve = 0 := by
    simpa [a, inv] using stride_sum_mod_twelve_zero amt
  calc
    rotPairNatAdd inv (rotPairNatAdd amt p)
        = rotPairNatAdd inv (rotPairNatAdd a p) := by
          rw [rotPairNatAdd_eq_rotPairNatAdd_amt_mod amt p]
    _ = rotPairNatAdd (a + inv) p :=
          (rotPairNatAdd_add_eq_rot_comp a inv p hp).symm
    _ = rotPairNatAdd ((a + inv) % twelve) p := by
          rw [← rotPairNatAdd_eq_rotPairNatAdd_amt_mod]
    _ = rotPairNatAdd 0 p := by rw [hz]
    _ = p := rotPairNatAdd_zero_pairsIJ p hp

theorem zmod_twelve_stride_inv_zero : zmodTwelveStrideInv 0 = 0 := by native_decide

/-- For **`0 < k < 12`**, the inverse stride is **`12 - k`**. -/
theorem zmod_twelve_stride_inv_eq_sub_of_pos_lt {k : Nat} (hk : k < twelve) (hk0 : 0 < k) :
    zmodTwelveStrideInv k = twelve - k := by
  simp only [zmodTwelveStrideInv, Nat.mod_eq_of_lt hk,
    Nat.mod_eq_of_lt (Nat.sub_lt twelve_pos hk0)]

end AeonTwelvePairsIJZmodAction
end Gnosis
