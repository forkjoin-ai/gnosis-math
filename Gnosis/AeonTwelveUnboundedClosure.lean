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

Likewise (**`pairsIJ`** chord labels via **`rotPairNatAdd`** from **`Gnosis.AeonTwelveCarrierList`**): **`12 ∣ k*s`** fixes every sorted pair **`p ∈ pairsIJ`**.

**Orbit characterization:** **`k`** successive **`rotPairNatAdd s`** ticks fix **every** gate in **`pairsIJ`** iff **`12 ∣ k*s`** — forward by **`iterateRotPairNatAddStride_eq_rot_nat_mul`** and **`rotPairNatAdd_eq_of_twelve_dvd`**, backward via the **`(0,1)`** pivot (**`pairsIJ_mem_axis_pair_01`** in **`Gnosis.AeonCycleTwelveShadow`**, **`chord_axis01_rot_moves_of_twelve_dvd_ne`**). Same clock as **full **`Fin 12`** deck **`k*s`** resets** (**`iterate_rot_stride_pairsIJ_fixed_iff_fin_vertices_fixed`**). Equivalent **`¬(12 ∣ k*s)`** witnesses some moving pair via **`exists_pairs_ij_iterate_stride_ne_iff_not_twelve_dvd_mul`** (**`(0,1)`** pivot), equivalently **`¬ strideTwelvePeriod s ∣ k`** (**`exists_pairs_ij_iterate_stride_ne_iff_not_strideTwelvePeriod_dvd`**). Equivalently **`strideTwelvePeriod s ∣ k`** (**`twelve_dvd_stride_mul_iff_stride_period_dvd`**).

Equivalent divisibility (**`Nat.Coprime`** on the reduced pair): **`12 ∣ k · s` ↔ `(12 / gcd(12,s)) ∣ k`** — so **`strideTwelvePeriod s`** serves as least positive **tick-multiplier** in the strict sense that every witness **`k`** is a multiple.

This is **`Nat`** repetition, not cardinality of `ℕ` nor analysis at infinity; naming is metaphorical.

Proofs stay **`Init`** on the shadow carrier; cofinal stride facts reuse **`twelve_dvd_mul_div_gcd_mul_s`** from **`Gnosis.AeonTwelveCarrierList`** once (no Mathlib).

**`2^7` cubes:** **`Gnosis.AeonTwelveResolutionSlotEmbedding`** supplies the **injective** gate-to-slot map
**`chordGateResolutionSlot`** (lex rank **`↔`** **`idxOf`**, then **`rowSlotFin128`**) plus the **Lagrange**
obstruction **`twelve_not_dvd_two_pow_seven`** on **`ℤ/128ℤ`**. Stride cofinality (**`12 ∣ k·s`**) governs **`rotPairNatAdd`**;
**`{0,1}^7`** Kauffman rows are a different book; these modules only interface where the story needs **shared indices** or
**forbidden homomorphisms**.
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

/-- **`12 ∣ k * s` ↔ `strideTwelvePeriod s ∣ k`**: tick-multiplier divisibility is the **`gcd`-reduced coprime** story. -/
theorem twelve_dvd_stride_mul_iff_stride_period_dvd (k s : Nat) :
    twelve ∣ k * s ↔ strideTwelvePeriod s ∣ k := by
  constructor
  · intro h
    let d := Nat.gcd twelve s
    let q := strideTwelvePeriod s
    have hqdef : twelve = d * q := (Nat.mul_div_cancel' (Nat.gcd_dvd_left twelve s)).symm
    have hdpos : 0 < d :=
      Nat.pos_of_ne_zero (Nat.gcd_ne_zero_left (m := twelve) (n := s) (Nat.succ_ne_zero 11))
    rcases Nat.gcd_dvd_right twelve s with ⟨sd, hs⟩
    rcases h with ⟨u, hu⟩
    have heq : d * (k * sd) = d * (q * u) := by
      have h₁ : d * (k * sd) = k * (d * sd) :=
        (Nat.mul_assoc d k sd).symm.trans
          ((congrArg (fun z => z * sd) (Nat.mul_comm d k)).trans (Nat.mul_assoc k d sd))
      calc
        d * (k * sd) = k * (d * sd) := h₁
        _ = k * s := congrArg (fun z => k * z) (Eq.symm hs)
        _ = twelve * u := hu
        _ = (d * q) * u := congrArg (fun x => x * u) hqdef
        _ = d * (q * u) := Nat.mul_assoc d q u
    have hksd : k * sd = q * u := Nat.mul_left_cancel hdpos heq
    have hsdivEq : s / d = sd := by
      calc
        s / d = (d * sd) / d := congrArg (· / d) hs
        _ = sd := Nat.mul_div_cancel_left sd hdpos
    have hqd : q ∣ k * sd := ⟨u, hksd⟩
    have hg1 : Nat.gcd q (s / d) = 1 := Nat.gcd_div_gcd_div_gcd_of_pos_left twelve_pos
    have hg1' : Nat.gcd q sd = 1 := by simpa [hsdivEq] using hg1
    have hcop : Nat.Coprime q sd := Nat.coprime_iff_gcd_eq_one.mpr hg1'
    exact Nat.Coprime.dvd_of_dvd_mul_right hcop hqd
  · rintro ⟨t, rfl⟩
    simpa [strideTwelvePeriod, Nat.mul_assoc, Nat.mul_comm t]
      using Nat.dvd_mul_right_of_dvd (twelve_dvd_mul_div_gcd_mul_s s) t

/-- Any **positive** tick count with **`12 ∣ k * s`** is at least **`strideTwelvePeriod s`**. -/
theorem stride_period_le_of_pos_dvd_stride_mul {k s : Nat} (hk : 0 < k) (h : twelve ∣ k * s) :
    strideTwelvePeriod s ≤ k :=
  Nat.le_of_dvd hk ((twelve_dvd_stride_mul_iff_stride_period_dvd k s).1 h)

/-- **`12 ∣ k*s`** restores **sorted** unordered chord endpoints on **`pairsIJ`** (gcd clock shared with **`Fin`** events). -/
theorem rotPairNatAdd_stride_product_fixes_pairsIJ (k s : Nat)
    (h : twelve ∣ k * s) (p : Nat × Nat) (hp : p ∈ pairsIJ) :
    rotPairNatAdd (k * s) p = p :=
  rotPairNatAdd_eq_of_twelve_dvd hp h

/-- **`k`** **`rotPairNatAdd s`** strides fix **all** **`pairsIJ`** labels iff **`12 ∣ k*s`**. -/
theorem iterate_rot_stride_fixes_pairsIJ_iff_twelve_dvd_mul (k s : Nat) :
    (∀ p ∈ pairsIJ, iterateRotPairNatAddStride s k p = p) ↔ twelve ∣ k * s := by
  refine ⟨fun hall => ?_, fun hdvd => ?_⟩
  · have hPivot :=
      (iterateRotPairNatAddStride_eq_rot_nat_mul k s (0, 1) pairsIJ_mem_axis_pair_01).symm.trans
        (hall (0, 1) pairsIJ_mem_axis_pair_01)
    by_cases h : k * s % twelve = 0
    · exact (Nat.dvd_iff_mod_eq_zero (m := twelve) (n := k * s)).2 h
    · exact absurd hPivot (chord_axis01_rot_moves_of_twelve_dvd_ne (k * s) h)
  · intro p hp
    rw [iterateRotPairNatAddStride_eq_rot_nat_mul k s p hp, rotPairNatAdd_eq_of_twelve_dvd hp hdvd]

/-- Same fixpoint characterization repackaged with **`strideTwelvePeriod`** (gcd-reduced multiplier). -/
theorem iterate_rot_stride_fixes_pairsIJ_iff_stride_period_dvd (k s : Nat) :
    (∀ p ∈ pairsIJ, iterateRotPairNatAddStride s k p = p) ↔ strideTwelvePeriod s ∣ k :=
  Iff.trans (iterate_rot_stride_fixes_pairsIJ_iff_twelve_dvd_mul k s)
    (twelve_dvd_stride_mul_iff_stride_period_dvd k s)

/-- **`Fin 12`** full deck **`k*s`** resets and **`pairsIJ`** **`k`**‑stride rotations share the **`12 ∣ k*s`** clock. -/
theorem iterate_rot_stride_pairsIJ_fixed_iff_fin_vertices_fixed (k s : Nat) :
    (∀ p ∈ pairsIJ, iterateRotPairNatAddStride s k p = p) ↔
      ∀ x : Fin twelve, iteratedCyclicSucc h12 (k * s) x = x :=
  (iterate_rot_stride_fixes_pairsIJ_iff_twelve_dvd_mul k s).trans
    (iterate_stride_product_all_vertices_iff_dvd k s).symm

/-- Pivot witness **`(0,1)`**: some **`pairsIJ`** label moves iff **`¬(12 ∣ k*s)`**. -/
theorem exists_pairs_ij_iterate_stride_ne_iff_not_twelve_dvd_mul (k s : Nat) :
    (∃ p ∈ pairsIJ, iterateRotPairNatAddStride s k p ≠ p) ↔ ¬ twelve ∣ k * s := by
  constructor
  · rintro ⟨p, hp, hpne⟩ hdvd
    have hfixed :
        iterateRotPairNatAddStride s k p = p :=
      (iterateRotPairNatAddStride_eq_rot_nat_mul k s p hp).trans (rotPairNatAdd_eq_of_twelve_dvd hp hdvd)
    exact hpne hfixed
  · intro hdvd
    refine ⟨(0, 1), pairsIJ_mem_axis_pair_01, ?_⟩
    rw [iterateRotPairNatAddStride_eq_rot_nat_mul k s _ pairsIJ_mem_axis_pair_01]
    have hm : k * s % twelve ≠ 0 := fun hz =>
      hdvd ((Nat.dvd_iff_mod_eq_zero (n := k * s)).mpr hz)
    exact chord_axis01_rot_moves_of_twelve_dvd_ne (k * s) hm

/-- Repackage **`exists_pairs_ij_iterate_stride_ne_iff_not_twelve_dvd_mul`** via **`twelve_dvd_stride_mul_iff_stride_period_dvd`**. -/
theorem exists_pairs_ij_iterate_stride_ne_iff_not_strideTwelvePeriod_dvd (k s : Nat) :
    (∃ p ∈ pairsIJ, iterateRotPairNatAddStride s k p ≠ p) ↔ ¬ strideTwelvePeriod s ∣ k :=
  Iff.trans (exists_pairs_ij_iterate_stride_ne_iff_not_twelve_dvd_mul k s)
    (not_congr (twelve_dvd_stride_mul_iff_stride_period_dvd k s))

end AeonTwelveUnboundedClosure
end Gnosis
