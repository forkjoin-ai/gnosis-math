import Init
import Gnosis.AeonCycleTwelveShadow
import Gnosis.AeonTwelveCarrierList

namespace Gnosis
namespace AeonTwelveUnboundedClosure

/-!
# Aeon-twelve trajectory: arbitrarily large multiples still close through the origin

**Infinityward (discrete-only):** for every **`anchor : Nat`** there exists a composite step-count
**`k ≥ anchor`** with **`12 ∣ k`**, hence **`iteratedCyclicSucc h12 k finZero = finZero`**
(full phase reset at event **0**) — the closed loop admits **no last return-time**: pick any finite
budget, multiply by **`twelve`** to land past it **and** on a modulus that kills **0**.

Stride packaging: with **`strideTwelvePeriod s := 12 / gcd(12,s)`** take **`k := strideTwelvePeriod s · anchor`**
so **`12 ∣ k · s`**, hence **`iteratedCyclicSucc h12 (k * s) finZero = finZero`** and, by **`dvd_iterate_fixed`**, **`iteratedCyclicSucc h12 (k * s) x = x`** for **every **`x : Fin 12`** (full deck reset).

This is **`Nat`** repetition, not cardinality of `ℕ` nor analysis at infinity; naming is metaphorical.

Proofs stay **`Init`** on the shadow carrier; cofinal stride facts reuse **`twelve_dvd_mul_div_gcd_mul_s`** from **`Gnosis.AeonTwelveCarrierList`** once (no Mathlib).
-/

open Gnosis.DiscreteClosedTimelikeStep
open Gnosis.AeonCycleTwelveShadow
open Gnosis.AeonTwelveCarrierList

theorem one_le_twelve : (1 : Nat) ≤ twelve := by decide

theorem anchor_le_twelve_anchor (anchor : Nat) : anchor ≤ twelve * anchor := by
  calc
    anchor = anchor * 1 := (Nat.mul_one anchor).symm
    _ ≤ anchor * twelve := Nat.mul_le_mul_left anchor one_le_twelve
    _ = twelve * anchor := Nat.mul_comm anchor twelve

/-- Above any finite **anchor**, some **composite** iterate length sits on the **twelve‑lattice**. -/
theorem arbitrarily_large_iterate_zero_fixed (anchor : Nat) :
    ∃ k : Nat,
      anchor ≤ k ∧ iteratedCyclicSucc h12 k finZero = finZero :=
  ⟨twelve * anchor,
    anchor_le_twelve_anchor anchor,
    (iterate_zero_fixed_iff_dvd _).2 (Nat.dvd_mul_right twelve anchor)⟩

theorem arbitrarily_large_iterate_zero_dvd (anchor : Nat) :
    ∃ k : Nat,
      anchor ≤ k ∧ twelve ∣ k ∧ iteratedCyclicSucc h12 k finZero = finZero :=
  ⟨twelve * anchor, anchor_le_twelve_anchor anchor, Nat.dvd_mul_right twelve anchor,
    (iterate_zero_fixed_iff_dvd _).2 (Nat.dvd_mul_right twelve anchor)⟩

/-! ### Periodic family: every **`12 · t`** is a modulus at the origin (not minimality).

The earlier **gcd / stride** story in **`AeonTwelveCarrierList`** pins *smaller* return times along
offsets; here we package only the cofinal **multiple-of-twelve** family—**infinityward** scaffolding.
-/

theorem iterate_zero_every_multiple_of_twelve (t : Nat) :
    iteratedCyclicSucc h12 (twelve * t) finZero = finZero :=
  (iterate_zero_fixed_iff_dvd _).2 (Nat.dvd_mul_right twelve t)

/-- Scaler **`12 / gcd(12,s)`** from **`twelve_dvd_mul_div_gcd_mul_s`**, packaged as cofinal stride period. -/
def strideTwelvePeriod (s : Nat) : Nat :=
  twelve / Nat.gcd twelve s

theorem stride_period_mul_anchor_shuffle (p a s : Nat) :
    (p * a) * s = (p * s) * a :=
  calc
    (p * a) * s = p * (a * s) := Nat.mul_assoc p a s
    _ = p * (s * a) := congrArg (fun z => p * z) (Nat.mul_comm a s)
    _ = (p * s) * a := (Nat.mul_assoc p s a).symm

theorem one_le_strideTwelvePeriod (s : Nat) : (1 : Nat) ≤ strideTwelvePeriod s := by
  rcases Nat.eq_zero_or_pos (strideTwelvePeriod s) with hz | hz
  · have hm : twelve = Nat.gcd twelve s * strideTwelvePeriod s :=
      Eq.symm (Nat.mul_div_cancel' (Nat.gcd_dvd_left twelve s))
    rw [hz] at hm
    rw [Nat.mul_zero] at hm
    exact absurd hm (Nat.ne_of_gt twelve_pos)
  · exact Nat.succ_le_of_lt hz

theorem anchor_le_stride_period_mul_anchor (anchor s : Nat) :
    anchor ≤ strideTwelvePeriod s * anchor := by
  rw [← Nat.mul_comm anchor (strideTwelvePeriod s)]
  calc
    anchor = anchor * 1 := (Nat.mul_one anchor).symm
    _ ≤ anchor * strideTwelvePeriod s := Nat.mul_le_mul_left anchor (one_le_strideTwelvePeriod s)

/-- Net **`gcd`-period** multiplier times **`anchor`** clears the stride product at the origin lattice. -/
theorem twelve_dvd_stride_period_scaled_product (anchor s : Nat) :
    twelve ∣ (strideTwelvePeriod s * anchor) * s := by
  rw [stride_period_mul_anchor_shuffle]
  exact Nat.dvd_mul_right_of_dvd (twelve_dvd_mul_div_gcd_mul_s s) anchor

/-- Cofinal **stride** resets at **finZero**, matching **`iteratedCyclicSucc h12 (k*s)`**. -/
theorem arbitrarily_large_stride_iterate_zero_fixed (anchor s : Nat) :
    ∃ k : Nat,
      anchor ≤ k ∧ iteratedCyclicSucc h12 (k * s) finZero = finZero :=
  ⟨strideTwelvePeriod s * anchor,
    anchor_le_stride_period_mul_anchor anchor s,
    (iterate_zero_fixed_iff_dvd _).2 (twelve_dvd_stride_period_scaled_product anchor s)⟩

theorem arbitrarily_large_stride_iterate_zero_dvd (anchor s : Nat) :
    ∃ k : Nat,
      anchor ≤ k ∧ twelve ∣ k * s ∧ iteratedCyclicSucc h12 (k * s) finZero = finZero :=
  let k := strideTwelvePeriod s * anchor
  have hk : anchor ≤ k := anchor_le_stride_period_mul_anchor anchor s
  have hdvd := twelve_dvd_stride_period_scaled_product anchor s
  ⟨k, hk, hdvd, (iterate_zero_fixed_iff_dvd _).2 hdvd⟩

/-- **`12 ∣ k * s`** characterizes **`k * s`**‑steps as a **full** deck shift on **`Fin 12`** (alias of `iterate_all_fixed_iff_dvd`). -/
theorem iterate_stride_product_all_vertices_iff_dvd (k s : Nat) :
    (∀ x : Fin twelve, iteratedCyclicSucc h12 (k * s) x = x) ↔ twelve ∣ k * s :=
  iterate_all_fixed_iff_dvd (k * s)

/-- Cofinally past **`anchor`**, **`k * stride`** steps fix **every** clock event (not merely **`finZero`**). -/
theorem arbitrarily_large_stride_iterate_fixed_all_vertices (anchor s : Nat) :
    ∃ k : Nat,
      anchor ≤ k ∧ ∀ x : Fin twelve, iteratedCyclicSucc h12 (k * s) x = x := by
  rcases arbitrarily_large_stride_iterate_zero_dvd anchor s with ⟨k, hk, hdvd, -⟩
  exact ⟨k, hk, fun x => dvd_iterate_fixed x (k * s) hdvd⟩

end AeonTwelveUnboundedClosure
end Gnosis
