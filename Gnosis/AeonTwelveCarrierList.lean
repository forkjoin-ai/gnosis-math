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

On **`pairsIJ`**, the same modulus **`12 ∣ k*s`** restores **sorted endpoint labels** (**`rotPairNatAdd (k*s) p = p`**) simultaneously with the **`Fin 12`** deck reset (**`dvd_iterate_fixed`**) --- one gcd clock rigidly couples vertices and unordered chord labels.

**Translation invariance:** **`shortChord (rotPairNatAdd m p) = shortChord p`** holds for every modulus **`m`**, extending the **`+1`** certificate (**`shortChord_rotPairNat_eq`**) rigidly forward from **`pairsIJ`**.

**Iterate versus sum:** on **`pairsIJ`**, **`rotPairNatAdd (a+b)`** matches **`rotPairNatAdd b` after **`rotPairNatAdd a`**, after rewriting by **`Nat.add_mod`** and reducing **`Nat % twelve`** to **`Fin twelve`** (**`native_decide`** seals the **`12² × 66`** enumeration).

**Column-label lists:** **`AeonCyclicPluckerLabels.rotatePluckerLabel`** (**global **`(+1) % 12`** on each index**) is **not** **`rotPairNatAdd`** (**translate both endpoints, then re-sort**): **`rot_pair_nat_add_one_packed_ne_rotate_plucker_label_counterexample`** below vs **`rotate_plucker_label_pairs_ij_ordered_gate_counterexample`** in **`AeonCycleTwelveShadow`**.

The **return time** certificate uses the product of twelve divided by gcd twelve s with s; it is one modulus hitting the origin, not a claim about smaller positive returns on other vertices (see `AeonCycleTwelveShadow`). Orbit-class headcounts on `pairsIJ` stay packaged as `countChord_eq_*` theorems in that same module.
-/

open AmplituhedronAttention.Grassmannian
open Gnosis.DiscreteClosedTimelikeStep
open Gnosis.AeonCycleTwelveShadow
open Gnosis.AeonStandingWaveCoordinateBridge
open Gnosis.AeonCyclicPluckerLabels

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

/-- Zero rejection vent yields godWeight thirteen when R is twelve. -/
theorem god_twelve_top_vent_eq_thirteen : godWeight twelve 0 = 13 := by
  native_decide

/-- Advance **both** coordinates by **`amt (mod 12)`**, then re-sort to **`i < j`** (column-clock shear on labels). -/
def rotPairNatAdd (amt : Nat) (p : Nat × Nat) : Nat × Nat :=
  let i := (p.1 + amt) % twelve
  let j := (p.2 + amt) % twelve
  if _ : i < j then (i, j) else (j, i)

/-- Rotate ordered pair endpoints by **`+1` mod twelve** --- one tick of **`rotPairNatAdd`**. -/
def rotPairNat (p : Nat × Nat) : Nat × Nat :=
  rotPairNatAdd 1 p

/-- **`rotPairNatAdd` depends only on the summand modulo twelve** --- same cyclic translation as column ticks. -/
theorem rotPairNatAdd_eq_rotPairNatAdd_amt_mod (amt : Nat) (p : Nat × Nat) :
    rotPairNatAdd amt p = rotPairNatAdd (amt % twelve) p := by
  have hi :=
    Eq.symm (Nat.add_mod_mod p.1 amt twelve)
  have hj :=
    Eq.symm (Nat.add_mod_mod p.2 amt twelve)
  simp only [rotPairNatAdd, hi, hj]

/-- Coordinate bounds on **`pairsIJ`** (**`AeonCycleTwelveShadow.pairsIJ_coords_lt_twelve`**). -/
theorem pairsIJ_coord_lt_twelve (p : Nat × Nat) (hp : p ∈ pairsIJ) :
    p.1 < twelve ∧ p.2 < twelve :=
  pairsIJ_coords_lt_twelve p hp

/-- Pivot chord **`{0, 1}`** lies in **`pairsIJ`** (**`native_decide`** on the enumerated list). -/
theorem pairsIJ_mem_axis_pair_01 : (0, 1) ∈ pairsIJ := by native_decide

/-- A **multiple of twelve** is a noop on **`pairsIJ`** coordinates (sorted labels stabilize with the **`Fin`** modulus). -/
theorem rotPairNatAdd_eq_of_twelve_dvd {amt : Nat} {p : Nat × Nat}
    (hp : p ∈ pairsIJ) (hamt : twelve ∣ amt) :
    rotPairNatAdd amt p = p := by
  rcases pairsIJ_coord_lt_twelve p hp with ⟨h1lt, h2lt⟩
  rcases hamt with ⟨t, rfl⟩
  have hi : (p.1 + twelve * t) % twelve = p.1 := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h1lt]
  have hj : (p.2 + twelve * t) % twelve = p.2 := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h2lt]
  simp only [rotPairNatAdd, hi, hj, dif_pos (pairsIJ_fst_lt_snd p hp)]

/-- Exhaustive cyclic certificate: amplitude depends only on **circular separation**, invariant under simultaneous translation **`+amt`**. -/
private theorem shortChord_rotPairNatAdd_eq_below_twelve_amt_aux :
    ∀ amt : Nat, amt < twelve → ∀ (p : Nat × Nat), p ∈ pairsIJ →
      shortChord (rotPairNatAdd amt p) = shortChord p := by
  intro amt _hlt p hp
  revert amt _hlt p hp
  native_decide

theorem shortChord_rotPairNatAdd_eq (m : Nat) (p : Nat × Nat) (hp : p ∈ pairsIJ) :
    shortChord (rotPairNatAdd m p) = shortChord p := by
  rw [rotPairNatAdd_eq_rotPairNatAdd_amt_mod m p]
  exact shortChord_rotPairNatAdd_eq_below_twelve_amt_aux _
    (Nat.mod_lt _ twelve_pos) p hp

theorem shortChord_rotPairNat_eq (p : Nat × Nat) (hp : p ∈ pairsIJ) :
    shortChord (rotPairNat p) = shortChord p :=
  shortChord_rotPairNatAdd_eq 1 p hp

/-- Applying **`+a`** then **`+b`** agrees with **`+ (a+b)`** on **`pairsIJ`** (finite **`native_decide`**). -/
private theorem rotPairNatAdd_add_aux (a' b' : Fin twelve) (p : Nat × Nat) (hp : p ∈ pairsIJ) :
    rotPairNatAdd ((a'.val + b'.val) % twelve) p =
      rotPairNatAdd b'.val (rotPairNatAdd a'.val p) := by
  revert a' b' p hp
  native_decide

theorem rotPairNatAdd_add_eq_rot_comp (a b : Nat) (p : Nat × Nat) (hp : p ∈ pairsIJ) :
    rotPairNatAdd (a + b) p = rotPairNatAdd b (rotPairNatAdd a p) := by
  rw [rotPairNatAdd_eq_rotPairNatAdd_amt_mod (a + b) p,
    rotPairNatAdd_eq_rotPairNatAdd_amt_mod b (rotPairNatAdd a p),
    rotPairNatAdd_eq_rotPairNatAdd_amt_mod a p]
  rw [Nat.add_mod a b twelve]
  let a' : Fin twelve := ⟨a % twelve, Nat.mod_lt _ twelve_pos⟩
  let b' : Fin twelve := ⟨b % twelve, Nat.mod_lt _ twelve_pos⟩
  simpa [a', b'] using rotPairNatAdd_add_aux a' b' p hp

/-! ### `rotatePluckerLabel` (**column-index list**) vs **`rotPairNatAdd`** (**sorted chord**)

**`rotatePluckerLabel`** acts on **gate lists** by **`rotateIndex = (· + 1) % 12`** entrywise **without**
restoring ascending **`i < j`** order. **`rotPairNatAdd`** translates **both** **`pairsIJ`** coordinates and
**re-sorts**. Shadow-side witness: **`rotate_plucker_label_pairs_ij_ordered_gate_counterexample`**.
-/

/-- Packed **`rotPairNatAdd 1`** (**sorted endpoints**) need not match **`rotatePluckerLabel [p.1, p.2]`**. -/
theorem rot_pair_nat_add_one_packed_ne_rotate_plucker_label_counterexample :
    ∃ p ∈ pairsIJ,
      [(rotPairNatAdd 1 p).1, (rotPairNatAdd 1 p).2] ≠ rotatePluckerLabel [p.1, p.2] := by
  native_decide

private theorem rotPairNatAdd_mem_pairsIJ_aux :
    ∀ amt : Nat,
      amt < twelve → ∀ (p : Nat × Nat), p ∈ pairsIJ → rotPairNatAdd amt p ∈ pairsIJ := by
  intro amt _hlt p hp
  revert amt _hlt p hp
  native_decide

theorem rotPairNatAdd_mem_pairsIJ (amt : Nat) (p : Nat × Nat) (hp : p ∈ pairsIJ) :
    rotPairNatAdd amt p ∈ pairsIJ := by
  rw [rotPairNatAdd_eq_rotPairNatAdd_amt_mod amt p]
  exact rotPairNatAdd_mem_pairsIJ_aux (amt % twelve) (Nat.mod_lt amt twelve_pos) p hp

/-- **`+0`** is the identity on **`pairsIJ`**. -/
theorem rotPairNatAdd_zero_pairsIJ (p : Nat × Nat) (hp : p ∈ pairsIJ) : rotPairNatAdd 0 p = p := by
  rcases pairsIJ_coord_lt_twelve p hp with ⟨h₁, h₂⟩
  dsimp [rotPairNatAdd]
  simp [Nat.mod_eq_of_lt h₁, Nat.mod_eq_of_lt h₂, pairsIJ_fst_lt_snd p hp]

/-- **`k`** successive **`rotPairNatAdd s`** ticks coincide with **`rotPairNatAdd (k*s)`** on **`pairsIJ`**. -/
def iterateRotPairNatAddStride (s : Nat) : Nat → Nat × Nat → Nat × Nat
  | 0, p => p
  | Nat.succ k, p =>
      iterateRotPairNatAddStride s k (rotPairNatAdd s p)

theorem iterateRotPairNatAddStride_eq_rot_nat_mul (k s : Nat) (p : Nat × Nat)
    (hp : p ∈ pairsIJ) :
    iterateRotPairNatAddStride s k p = rotPairNatAdd (k * s) p := by
  revert p hp
  induction k with
  | zero =>
    intro p hp
    dsimp [iterateRotPairNatAddStride]
    rw [Nat.zero_mul]
    symm
    exact rotPairNatAdd_zero_pairsIJ p hp
  | succ k ih =>
    intro p hp
    dsimp [iterateRotPairNatAddStride]
    have hpRot : rotPairNatAdd s p ∈ pairsIJ := rotPairNatAdd_mem_pairsIJ s p hp
    have hs_len : s + k * s = (k + 1) * s := by
      rw [Nat.add_comm]
      rw [← Nat.succ_mul k s]
    calc
      iterateRotPairNatAddStride s k (rotPairNatAdd s p)
          = rotPairNatAdd (k * s) (rotPairNatAdd s p) := ih (rotPairNatAdd s p) hpRot
      _ = rotPairNatAdd (s + k * s) p := (rotPairNatAdd_add_eq_rot_comp s (k * s) p hp).symm
      _ = rotPairNatAdd ((k + 1) * s) p :=
        congrArg (fun t => rotPairNatAdd t p) hs_len

private theorem chord_axis01_not_fixed_below_twelve_amt_aux :
    ∀ amt : Nat, amt < twelve → 0 < amt →
      rotPairNatAdd amt (0, 1) ≠ (0, 1) := by
  intro amt _h₁ _h₀
  revert amt _h₁ _h₀
  native_decide

/-- Pivot chord **`{0,1}`**: any **non‑zero modulus below twelve** nudges **`pairsIJ`** (legacy name; hyphen reads oddly next to gcd narrative). -/
theorem chord_axis01_rot_moves_of_twelve_dvd_ne (amt : Nat) (hm : amt % twelve ≠ 0) :
    rotPairNatAdd amt (0, 1) ≠ (0, 1) := by
  have hlt : amt % twelve < twelve := Nat.mod_lt amt twelve_pos
  have h₀ : 0 < amt % twelve := Nat.pos_of_ne_zero hm
  have := chord_axis01_not_fixed_below_twelve_amt_aux (amt % twelve) hlt h₀
  simpa [rotPairNatAdd_eq_rotPairNatAdd_amt_mod amt (0, 1)]

/-- Same as **`chord_axis01_rot_moves_of_twelve_dvd_ne`**, with **`amt % twelve ≠ 0`** spelled as the hypothesis label (no **`dvd`** wording). -/
theorem chord_axis01_rot_moves_of_amt_mod_ne_zero (amt : Nat) (hm : amt % twelve ≠ 0) :
    rotPairNatAdd amt (0, 1) ≠ (0, 1) :=
  chord_axis01_rot_moves_of_twelve_dvd_ne amt hm

theorem shortChord_attains_six_values :
    (∃ p ∈ pairsIJ, shortChord p = 1) ∧
      (∃ p ∈ pairsIJ, shortChord p = 2) ∧
        (∃ p ∈ pairsIJ, shortChord p = 3) ∧
          (∃ p ∈ pairsIJ, shortChord p = 4) ∧
            (∃ p ∈ pairsIJ, shortChord p = 5) ∧
              (∃ p ∈ pairsIJ, shortChord p = 6) := by
  native_decide

end AeonTwelveCarrierList
end Gnosis
