import Init
import Gnosis.CircadianGnosisAlignment
import Gnosis.DiscreteClosedTimelikeStep
import Gnosis.AeonCyclicPluckerLabels
import Gnosis.AmplituhedronGrassmannian

namespace Gnosis
namespace AeonCycleTwelveShadow

/-!
# Twelve-cycle shadow: chords, **66** pairs, Plücker count, modular fixes

Modulus **`n = Circadian.aeon = 12`** with rotation from `DiscreteClosedTimelikeStep`.

## Chord

`circChordAux` is **rot-invariant** (`circChordAux_rot`) — shadow of **translation on `ℤ/12ℤ`**.

## **66** (different sets, same cardinal)

* `pairsIJ` — unordered **`i < j`**, length **66**.
* `kSubsets 2 12` — ordered Plücker labels, length **66**.
* **`pairs_ij_ordered_plucker_labels`** packs **`pairsIJ`** as **`[i, j]`** lists; **`mem_kSubsets_two_twelve_iff_mem_pairs_ij_ordered_labels`**
  matches membership (**same 66 gates**, possibly different list order).
* **`rotatePluckerLabel`** (**`AeonCyclicPluckerLabels`**) shifts **each column index** mod **12** without re-sorting (**`pair_mem_pairsIJ_iff_fst_lt_snd`**, **`list_pair_mem_pairsIJOrderedPluckerLabels_iff`**, **`pairsIJ_coords_lt_twelve`**, **`rotate_plucker_label_mem_*_iff_rotate_index_lt`** / **`_mem`** record **`kSubsets` / `pairsIJ`** alignment); **`rotate_plucker_label_pairs_ij_ordered_gate_counterexample`** gives failure mode. **`rotPairNatAdd`** (**`AeonTwelveCarrierList`**) --- **`rot_pair_nat_add_one_packed_ne_rotate_plucker_label_counterexample`** there.

## Distance classes

`shortChord` on `pairsIJ` yields per-class counts **12,12,12,12,12,6**.

## Modular return

`iteratedCyclicSucc h12 m` is the **identity map** on **`Fin 12`** iff **`12 ∣ m`**
(`iterate_all_fixed_iff_dvd`).
For **`m = k * s`**, equivalently **`12 ∣ k*s` ↔ `(12 / gcd(12,s)) ∣ k`** on **`Nat`**
via `AeonTwelveUnboundedClosure.twelve_dvd_stride_mul_iff_stride_period_dvd`.
Sorted **`pairsIJ`** labels stabilize under the **same modulus** (**`rotPairNatAdd`** in `AeonTwelveCarrierList`,
packaged cofinally by `rotPairNatAdd_stride_product_fixes_pairsIJ`).
**Iterate vs product:** **`k`** **`rotPairNatAdd s`** steps fix **all** **`pairsIJ`** gates iff **`12 ∣ k*s`** (equivalently **`strideTwelvePeriod s ∣ k`**) ---
`iterate_rot_stride_fixes_pairsIJ_iff_twelve_dvd_mul`, `iterate_rot_stride_fixes_pairsIJ_iff_stride_period_dvd` in `AeonTwelveUnboundedClosure`; some gate moves iff **`¬(12 ∣ k*s)`** / **`¬ strideTwelvePeriod s ∣ k`** ---
`exists_pairs_ij_iterate_stride_ne_iff_not_twelve_dvd_mul`, `exists_pairs_ij_iterate_stride_ne_iff_not_strideTwelvePeriod_dvd`.
Chord class (**`shortChord`**) does not change under any simultaneous translation modulus **`m`**, and two translations compose like **`ℤ/12ℤ`** (**`shortChord_rotPairNatAdd_eq`**, **`rotPairNatAdd_add_eq_rot_comp`** there).

See `Gnosis.AeonTwelveCarrierList` for the **ordered** gcd / Plücker / `godWeight` / pair-rotation
list built on top of this shadow.

`Gnosis.AeonTwelveUnboundedClosure` states **cofinal** multiples of twelve at **`finZero`** and **cofinal**
**`k · s`** net lengths past any **`anchor`**, with the same **`12 ∣ k*s`** modulus fixing **all** **`Fin 12`**
events (**`dvd_iterate_fixed`**), anchored on **`strideTwelvePeriod`** and **`AeonTwelveCarrierList`**, still Init-only beside this shadow.
-/

def twelve : Nat :=
  12

theorem twelve_pos : 0 < twelve :=
  Nat.succ_pos _

abbrev h12 : 0 < twelve :=
  twelve_pos

theorem twelve_eq_aeon : twelve = Circadian.aeon :=
  rfl

open Gnosis.DiscreteClosedTimelikeStep
open AmplituhedronAttention.Grassmannian

abbrev rot : Fin twelve → Fin twelve :=
  cyclicSucc h12

def cwSpan (a b : Fin twelve) : Nat :=
  (b.val + twelve - a.val) % twelve

def circChordAux (a b : Fin twelve) : Nat :=
  let f := cwSpan a b
  min f (twelve - f)

theorem circChordAux_rot : ∀ a b : Fin twelve,
    circChordAux a b = circChordAux (rot a) (rot b) := by
  native_decide

theorem circChordAux_pos {a b : Fin twelve} (hab : a ≠ b) : 0 < circChordAux a b := by
  revert a b hab
  native_decide

def pairsIJ : List (Nat × Nat) :=
  (List.range twelve).flatMap fun i : Nat =>
    (List.range twelve).filterMap fun j : Nat =>
      if i < j then some (i, j) else none

theorem pairsIJ_length : pairsIJ.length = 66 := by
  native_decide

theorem pairsIJ_fst_lt_snd (p : Nat × Nat) (hp : p ∈ pairsIJ) : p.1 < p.2 := by
  revert p hp
  native_decide

/-- Both chord endpoints lie in **`0 … eleven`** (**`pairsIJ`** enumeration witness).

**Call-site alias:** **`Gnosis.AeonTwelveCarrierList.pairsIJ_coord_lt_twelve`**. -/
theorem pairsIJ_coords_lt_twelve (p : Nat × Nat) (hp : p ∈ pairsIJ) :
    p.1 < twelve ∧ p.2 < twelve := by
  revert p hp
  native_decide

theorem kSubsets_two_twelve_length : (kSubsets 2 twelve).length = 66 := by
  native_decide

theorem pluckerLabelCount_eq_pairsIJ : (kSubsets 2 twelve).length = pairsIJ.length := by
  rw [kSubsets_two_twelve_length, pairsIJ_length]

/-- Repackage **`pairsIJ`** entries as ascending length-**2** column lists (**Plücker gate** shape). -/
def pairsIJOrderedPluckerLabels : List (List Nat) :=
  pairsIJ.map (fun p => [p.1, p.2])

theorem pairs_ij_ordered_plucker_labels_length :
    pairsIJOrderedPluckerLabels.length = 66 := by
  simp only [pairsIJOrderedPluckerLabels, List.length_map, pairsIJ_length]

/-- Every **`kSubsets 2 twelve`** label arises from some **`pairsIJ`** pair (**surjective** onto the packed list). -/
theorem kSubsets_two_twelve_mem_pairs_ij_ordered_labels (cols : List Nat)
    (hcols : cols ∈ kSubsets 2 twelve) :
    cols ∈ pairsIJOrderedPluckerLabels := by
  revert cols hcols
  native_decide

/-- Every packed **`pairsIJ`** label is a **`kSubsets 2 twelve`** gate (**Plücker enumeration**). -/
theorem pairs_ij_ordered_labels_mem_kSubsets_two_twelve (cols : List Nat)
    (hcols : cols ∈ pairsIJOrderedPluckerLabels) :
    cols ∈ kSubsets 2 twelve := by
  revert cols hcols
  native_decide

/-- **`kSubsets`** membership ↔ **`pairsIJ`** row repacked as **`[i, j]`** (**66**-label bridge). -/
theorem mem_kSubsets_two_twelve_iff_mem_pairs_ij_ordered_labels (cols : List Nat) :
    cols ∈ kSubsets 2 twelve ↔ cols ∈ pairsIJOrderedPluckerLabels :=
  ⟨fun h => kSubsets_two_twelve_mem_pairs_ij_ordered_labels cols h,
    fun h => pairs_ij_ordered_labels_mem_kSubsets_two_twelve cols h⟩

/-- Direct extract: **`p ∈ pairsIJ`** ⇒ **`[p.1, p.2] ∈ kSubsets 2 twelve`**. -/
theorem pairs_ij_pair_ordered_mem_kSubsets_two_twelve (p : Nat × Nat) (hp : p ∈ pairsIJ) :
    [p.1, p.2] ∈ kSubsets 2 twelve := by
  revert p hp
  native_decide

/-- **`kSubsets`** label unpacks to some **`p ∈ pairsIJ`** with **`[p.1, p.2] = cols`**. -/
theorem kSubsets_two_twelve_exists_pairs_ij (cols : List Nat) (hcols : cols ∈ kSubsets 2 twelve) :
    ∃ p ∈ pairsIJ, [p.1, p.2] = cols := by
  revert cols hcols
  native_decide

/-! ## Column-label rotation (`AeonCyclicPluckerLabels`) vs ascending **`pairsIJ`** packing

**`rotatePluckerLabel`** applies **`rotateIndex = (· + 1) % 12`** to every entry of a label list.
That is **not** the same operation as **`rotPairNatAdd`** on **`pairsIJ`**, which translates **both**
endpoints then **re-sorts** to **`i < j`**.

For **`i < j`** with **`i, j < twelve`**, **`rotatePluckerLabel [i, j]`** lies in **`pairsIJOrderedPluckerLabels`**
(equivalently **`kSubsets 2 twelve`**) **iff** **`rotateIndex i < rotateIndex j`**
(**`rotate_plucker_label_mem_pairs_ij_ordered_labels_iff_rotate_index_lt`**,
**`rotate_plucker_label_mem_kSubsets_two_twelve_iff_rotate_index_lt`**).
-/

theorem rotate_plucker_label_pair_eq_map_rotateIndex (i j : Nat) :
    AeonCyclicPluckerLabels.rotatePluckerLabel [i, j] =
      [AeonCyclicPluckerLabels.rotateIndex i, AeonCyclicPluckerLabels.rotateIndex j] :=
  rfl

theorem rotate_all_pairs_ij_ordered_labels_length_eq :
    (AeonCyclicPluckerLabels.rotateAllPluckerLabels pairsIJOrderedPluckerLabels).length = 66 := by
  rw [AeonCyclicPluckerLabels.rotateAll_length, pairs_ij_ordered_plucker_labels_length]

/-- Some **`p ∈ pairsIJ`** has **`rotatePluckerLabel [p.1, p.2]`** **not** back in **`pairsIJOrderedPluckerLabels`**
(entrywise **`+1`** can invert the **`i < j`** list order). -/
theorem rotate_plucker_label_pairs_ij_ordered_gate_counterexample :
    ∃ p ∈ pairsIJ,
      AeonCyclicPluckerLabels.rotatePluckerLabel [p.1, p.2] ∉ pairsIJOrderedPluckerLabels := by
  native_decide

/-- **`pairsIJ`** membership for endpoints **`a, b < twelve`** is **`a < b`**. -/
theorem pair_mem_pairsIJ_iff_fst_lt_snd (a b : Nat) (ha : a < twelve) (hb : b < twelve) :
    (a, b) ∈ pairsIJ ↔ a < b := by
  constructor
  · intro h
    exact pairsIJ_fst_lt_snd (a, b) h
  · intro hab
    dsimp [pairsIJ]
    rw [List.mem_flatMap]
    refine ⟨a, List.mem_range.mpr ha, ?_⟩
    rw [List.mem_filterMap]
    refine ⟨b, List.mem_range.mpr hb, ?_⟩
    simp [hab]

/-- Ascending length-**2** list **`[a, b]`** lies in **`pairsIJOrderedPluckerLabels`** iff **`(a, b) ∈ pairsIJ`**. -/
theorem list_pair_mem_pairsIJOrderedPluckerLabels_iff (a b : Nat) (ha : a < twelve) (hb : b < twelve) :
    [a, b] ∈ pairsIJOrderedPluckerLabels ↔ (a, b) ∈ pairsIJ := by
  unfold pairsIJOrderedPluckerLabels
  constructor
  · intro hm
    rcases List.mem_map.mp hm with ⟨⟨p1, p2⟩, hp, heq⟩
    simp [List.cons.injEq] at heq
    rcases heq with ⟨rfl, rfl⟩
    exact hp
  · intro hp
    exact List.mem_map.mpr ⟨(a, b), hp, rfl⟩

/-- For **`i < j`** with **`i, j < twelve`**, rotated gate **`[rotateIndex i, rotateIndex j]`** lies in the **`pairsIJ`**
packing **iff** **`rotateIndex i < rotateIndex j`** (equivalently: ascending **Plücker** column order is preserved). -/
theorem rotate_plucker_label_mem_pairs_ij_ordered_labels_iff_rotate_index_lt (i j : Nat)
    (_hij : i < j) (_hi : i < twelve) (_hj : j < twelve) :
    AeonCyclicPluckerLabels.rotatePluckerLabel [i, j] ∈ pairsIJOrderedPluckerLabels ↔
      AeonCyclicPluckerLabels.rotateIndex i < AeonCyclicPluckerLabels.rotateIndex j := by
  rw [rotate_plucker_label_pair_eq_map_rotateIndex]
  have hri : AeonCyclicPluckerLabels.rotateIndex i < twelve :=
    Nat.mod_lt (i + 1) twelve_pos
  have hrj : AeonCyclicPluckerLabels.rotateIndex j < twelve :=
    Nat.mod_lt (j + 1) twelve_pos
  rw [list_pair_mem_pairsIJOrderedPluckerLabels_iff _ _ hri hrj, pair_mem_pairsIJ_iff_fst_lt_snd _ _ hri hrj]

/-- Same criterion via **`kSubsets 2 twelve`** (**`mem_kSubsets_two_twelve_iff_mem_pairs_ij_ordered_labels`**). -/
theorem rotate_plucker_label_mem_kSubsets_two_twelve_iff_rotate_index_lt (i j : Nat)
    (hij : i < j) (hi : i < twelve) (hj : j < twelve) :
    AeonCyclicPluckerLabels.rotatePluckerLabel [i, j] ∈ kSubsets 2 twelve ↔
      AeonCyclicPluckerLabels.rotateIndex i < AeonCyclicPluckerLabels.rotateIndex j := by
  rw [mem_kSubsets_two_twelve_iff_mem_pairs_ij_ordered_labels,
    rotate_plucker_label_mem_pairs_ij_ordered_labels_iff_rotate_index_lt i j hij hi hj]

/-- **`p ∈ pairsIJ`**: rotated packed chord stays in **`pairsIJOrderedPluckerLabels`** iff **`rotateIndex`** order. -/
theorem rotate_plucker_label_mem_pairs_ij_ordered_labels_iff_rotate_index_lt_mem (p : Nat × Nat)
    (hp : p ∈ pairsIJ) :
    AeonCyclicPluckerLabels.rotatePluckerLabel [p.1, p.2] ∈ pairsIJOrderedPluckerLabels ↔
      AeonCyclicPluckerLabels.rotateIndex p.1 < AeonCyclicPluckerLabels.rotateIndex p.2 := by
  rcases pairsIJ_coords_lt_twelve p hp with ⟨hi, hj⟩
  exact rotate_plucker_label_mem_pairs_ij_ordered_labels_iff_rotate_index_lt p.1 p.2
    (pairsIJ_fst_lt_snd p hp) hi hj

/-- **`kSubsets`** packaging of **`rotate_plucker_label_mem_pairs_ij_ordered_labels_iff_rotate_index_lt_mem`**. -/
theorem rotate_plucker_label_mem_kSubsets_two_twelve_iff_rotate_index_lt_mem (p : Nat × Nat)
    (hp : p ∈ pairsIJ) :
    AeonCyclicPluckerLabels.rotatePluckerLabel [p.1, p.2] ∈ kSubsets 2 twelve ↔
      AeonCyclicPluckerLabels.rotateIndex p.1 < AeonCyclicPluckerLabels.rotateIndex p.2 := by
  rw [mem_kSubsets_two_twelve_iff_mem_pairs_ij_ordered_labels,
    rotate_plucker_label_mem_pairs_ij_ordered_labels_iff_rotate_index_lt_mem p hp]

/-- Under **`rotateIndex i < rotateIndex j`**, the rotated endpoints form a **`pairsIJ`** chord directly. -/
theorem rotate_index_lt_pair_mem_pairsIJ (i j : Nat) (_hij : i < j) (_hi : i < twelve) (_hj : j < twelve)
    (hord : AeonCyclicPluckerLabels.rotateIndex i < AeonCyclicPluckerLabels.rotateIndex j) :
    (AeonCyclicPluckerLabels.rotateIndex i, AeonCyclicPluckerLabels.rotateIndex j) ∈ pairsIJ := by
  have hri : AeonCyclicPluckerLabels.rotateIndex i < twelve :=
    Nat.mod_lt (i + 1) twelve_pos
  have hrj : AeonCyclicPluckerLabels.rotateIndex j < twelve :=
    Nat.mod_lt (j + 1) twelve_pos
  exact (pair_mem_pairsIJ_iff_fst_lt_snd _ _ hri hrj).mpr hord

/-- Rotate endpoints land on **`pairsIJ`** from **`p ∈ pairsIJ`** + ascending **`rotateIndex`**. -/
theorem rotate_index_pair_mem_pairsIJ_of_mem (p : Nat × Nat) (hp : p ∈ pairsIJ)
    (hord : AeonCyclicPluckerLabels.rotateIndex p.1 < AeonCyclicPluckerLabels.rotateIndex p.2) :
    (AeonCyclicPluckerLabels.rotateIndex p.1, AeonCyclicPluckerLabels.rotateIndex p.2) ∈ pairsIJ := by
  rcases pairsIJ_coords_lt_twelve p hp with ⟨hi, hj⟩
  exact rotate_index_lt_pair_mem_pairsIJ p.1 p.2 (pairsIJ_fst_lt_snd p hp) hi hj hord

def shortChord (p : Nat × Nat) : Nat :=
  let d := p.2 - p.1
  min d (twelve - d)

theorem countChord_eq_one : (pairsIJ.filter (fun p => shortChord p = 1)).length = 12 := by
  native_decide

theorem countChord_eq_two : (pairsIJ.filter (fun p => shortChord p = 2)).length = 12 := by
  native_decide

theorem countChord_eq_three : (pairsIJ.filter (fun p => shortChord p = 3)).length = 12 := by
  native_decide

theorem countChord_eq_four : (pairsIJ.filter (fun p => shortChord p = 4)).length = 12 := by
  native_decide

theorem countChord_eq_five : (pairsIJ.filter (fun p => shortChord p = 5)).length = 12 := by
  native_decide

theorem countChord_eq_six : (pairsIJ.filter (fun p => shortChord p = 6)).length = 6 := by
  native_decide

theorem distClass_counts_sum : 12 + 12 + 12 + 12 + 12 + 6 = 66 :=
  rfl

def finZero : Fin twelve :=
  ⟨0, Nat.zero_lt_succ 11⟩

theorem iterate_zero_fixed_iff_dvd (m : Nat) :
    iteratedCyclicSucc h12 m finZero = finZero ↔ twelve ∣ m := by
  constructor
  · intro h
    have hv : (iteratedCyclicSucc h12 m finZero).val = finZero.val :=
      congrArg Fin.val h
    rw [iteratedCyclicSucc_val] at hv
    rw [show finZero.val = (0 : Nat) from rfl, Nat.zero_add] at hv
    rwa [Nat.dvd_iff_mod_eq_zero]
  · intro hm
    rw [Nat.dvd_iff_mod_eq_zero] at hm
    apply Fin.ext
    rw [iteratedCyclicSucc_val, show finZero.val = (0 : Nat) from rfl, Nat.zero_add]
    exact hm

theorem dvd_iterate_fixed (x : Fin twelve) (m : Nat) (hm : twelve ∣ m) :
    iteratedCyclicSucc h12 m x = x := by
  rcases hm with ⟨k, rfl⟩
  apply Fin.ext
  rw [iteratedCyclicSucc_val]
  simp [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt x.isLt]

theorem iterate_all_fixed_iff_dvd (m : Nat) :
    (∀ x : Fin twelve, iteratedCyclicSucc h12 m x = x) ↔ twelve ∣ m := by
  constructor
  · intro hall
    have hz := hall finZero
    exact (iterate_zero_fixed_iff_dvd m).1 hz
  · intro hm x
    exact dvd_iterate_fixed x m hm

end AeonCycleTwelveShadow
end Gnosis
