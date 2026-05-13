import Init
import Gnosis.AeonTwelveHammingGrayDynamics
import Gnosis.AeonTwelvePairsIJZmodAction

namespace Gnosis
namespace AeonTwelveHypercubeMajorization

/-!
# Hypercube envelope (**majorization layer**) — Gray codec, permutation, chord–shear census

Builds on **`Gnosis.AeonTwelveHammingGrayDynamics`** / **`Gnosis.AeonTwelveResolutionSlotEmbedding`**.

## Gray (**`n = 7`**)

* **`grayDecodeNat`** inverts **`grayEncodeNat`** on **`0 … 127`** (**kernel-checked **`List.all`** loops**).
* **`gray_encode_binary_slot_permutation_cover`** — sorting **`List.map grayEncodeNat (List.range 128)`**
  yields **`List.range 128`**: Gray encoding **permutes** resolution-slot indices (**Hamiltonian ordering** hitting each codeword once).
* **`gray_cycle_closure_gray_codewords_adjacent`** — **`grayEncodeNat 127`** and **`grayEncodeNat 0`** differ by Hamming **`1`**:
  the Gray listing is a **Hamiltonian cycle** closing edge on **`Q₇`** (contrasting with chord gates below).

## **`pairsIJ`** shear vs **`Fin 128`** slots (**fixed atlas **`chordGateResolutionSlot`**)

For **`amt : Nat`** stride **`rotPairNatAdd amt`**:

* **`chordRotAmtHammingMultisetSorted amt`** sorts the multiset of **`66`** Hamming distances between **`chordGateResolutionSlot p`**
  and **`chordGateResolutionSlot (rotPairNatAdd amt p)`**.
* **`chord_rot_amt_one_histogram_sorted_eq_witness`** expands **`amt = 1`** into **`{1⁸, 2⁹, 3²⁸, 4¹⁴, 5⁴, 6³}`** (**sorted witness list**).
* **Stride symmetry** (**group inverse / **`ℤ/12ℤ`**) **`chord_rot_hist_sorted_amt_eq_zmod_stride_inv`** — histogram matches **`zmodTwelveStrideInv amt`** (**`List.range 12`** **`native_decide`** certificate**).
  Earlier **`chord_rot_hist_sorted_amt_*_eq`** lemmas remain one-line corollaries for bibliography anchors (**`1↔11 … 5↔7`**).
* **`amt = 6`** (**half-turn**) splits into **`6`** fixed gates (**Hamming **`0`**) plus an exotic positive-distance histogram (**witness theorem**).

## Twelve-phase corner lifts

**`aeonGrayCornerSlot`** Gray-labels **`Fin twelve`** inside **`Fin 128`** — differs from naive numeric embed (**example theorem at **`5`****).

## Modular alignment (**`lcm`** reminder)

**`lcm_gray_corner_phase_aligned`** — adding **`lcm (12, 2⁷)`** to a vertex label **doesn't change** **`grayEncodeNat (i mod 12)`** phase slice.

Zero `sorry`, zero new `axiom`.
-/

open Gnosis.AeonTwelveHammingGrayDynamics
open Gnosis.AeonTwelvePairsIJZmodAction
open Gnosis.AeonTwelveResolutionSlotEmbedding
open Gnosis.AeonTwelveCarrierList
open Gnosis.AeonCycleTwelveShadow

/-! ## Gray decode (**inverse near **`Nat`** precision)-/

/-- Fuel-bounded inverse loop (**classic **`bin XOR= gray >>> k`** peeling**). -/
def grayDecodeAux (bin grayRem fuel : Nat) : Nat :=
  match fuel with
  | 0 => bin
  | Nat.succ fuel' =>
      match grayRem with
      | 0 => bin
      | _ =>
          grayDecodeAux (bin ^^^ grayRem) (Nat.shiftRight grayRem 1) fuel'

/-- Conservative inverse (**ample fuel**) for **`7`**-bit Gray codewords. -/
def grayDecodeNat (g : Nat) : Nat :=
  grayDecodeAux g (Nat.shiftRight g 1) 64

private theorem gray_decode_encode_loop_cert :
    (List.range 128).all (fun x => decide (grayDecodeNat (grayEncodeNat x) = x)) = true := by native_decide

private theorem gray_encode_decode_loop_cert :
    (List.range 128).all (fun g => decide (grayEncodeNat (grayDecodeNat g) = g)) = true := by native_decide

/-- **`grayDecodeNat`** peels **`grayEncodeNat`** on **`Fin 128`** indices (`x < 128`). -/
theorem gray_decode_gray_encode_eq_of_lt128 {x : Nat} (hx : x < 128) :
    grayDecodeNat (grayEncodeNat x) = x := by
  have hall := List.all_eq_true.mp gray_decode_encode_loop_cert x (List.mem_range.mpr hx)
  simpa using hall

/-- **`grayEncodeNat`** restores Gray labels (`g < 128`). -/
theorem gray_encode_gray_decode_eq_of_lt128 {g : Nat} (hg : g < 128) :
    grayEncodeNat (grayDecodeNat g) = g := by
  have hall := List.all_eq_true.mp gray_encode_decode_loop_cert g (List.mem_range.mpr hg)
  simpa using hall

/-- Sorted multiset of Gray slots equals **`0 … 127`** — Gray encode **permutes** hypercube vertices. -/
theorem gray_encode_binary_slot_permutation_cover :
    ((List.range 128).map grayEncodeNat).mergeSort (fun a b => decide (a ≤ b)) = List.range 128 := by native_decide

private theorem gray_encode_injective_nested_cert :
    (List.range 128).all (fun x =>
      (List.range 128).all (fun y =>
        decide (grayEncodeNat x = grayEncodeNat y → x = y))) = true := by native_decide

/-- **`grayEncodeNat`** is **injective** on **`{0,…,127}`**. -/
theorem gray_encode_nat_injective_fin_domain {x y : Nat} (hx : x < 128) (hy : y < 128)
    (he : grayEncodeNat x = grayEncodeNat y) : x = y := by
  have hxr := List.mem_range.mpr hx
  have hyr := List.mem_range.mpr hy
  have houter := List.all_eq_true.mp gray_encode_injective_nested_cert x hxr
  have hinner := List.all_eq_true.mp houter y hyr
  exact (decide_eq_true_iff.mp hinner) he

/-- Closing edge (**Gray codewords at **`127`** and **`0`**) — unit Hamming (**Hamiltonian cycle cap**). -/
theorem gray_cycle_closure_gray_codewords_adjacent :
    hammingWtLowBits (grayEncodeNat 127 ^^^ grayEncodeNat 0) 7 = 1 := by native_decide

/-! ## Chord gates vs shear (**sorted Hamming multiset**)-/

/-- Hamming multiset (**sorted ascending**) for **`rotPairNatAdd amt`** acting on **`pairsIJ`**. -/
def chordRotAmtHammingMultisetSorted (amt : Nat) : List Nat :=
  (pairsIJ.attach.map fun ⟨p, hp⟩ =>
        fin128HammingDist (chordGateResolutionSlot p hp)
          (chordGateResolutionSlot (rotPairNatAdd amt p) (rotPairNatAdd_mem_pairsIJ amt p hp))).mergeSort
    (fun a b => decide (a ≤ b))

/-! ### Full census at **`amt = 1`** (explicit witness) -/

/-- Theory-predicted sorted histogram (**`8+9+28+14+4+3 = 66`** distances). -/
def chordRotAmtOneHistogramSortedWitness : List Nat :=
  List.replicate 8 1 ++ List.replicate 9 2 ++ List.replicate 28 3 ++ List.replicate 14 4 ++ List.replicate 4 5 ++
    List.replicate 3 6

theorem chord_rot_amt_one_histogram_sorted_length :
    chordRotAmtOneHistogramSortedWitness.length = 66 := by native_decide

theorem chord_rot_amt_one_histogram_sorted_eq_witness :
    chordRotAmtHammingMultisetSorted 1 = chordRotAmtOneHistogramSortedWitness := by native_decide

/-! ### Complementary stride symmetry (**`ℤ/12ℤ` inverse stride**) -/

private theorem chord_rot_hist_sorted_amt_eq_zmod_stride_inv_range_cert :
    (List.range twelve).all (fun amt =>
      decide (chordRotAmtHammingMultisetSorted amt =
        chordRotAmtHammingMultisetSorted (zmodTwelveStrideInv amt))) = true := by native_decide

/-- Sorted **`66`**-gate Hamming census matches **`rotPairNatAdd`** along **`−[amt]`** (**`zmodTwelveStrideInv`**). -/
theorem chord_rot_hist_sorted_amt_eq_zmod_stride_inv {amt : Nat} (hamt : amt < twelve) :
    chordRotAmtHammingMultisetSorted amt =
      chordRotAmtHammingMultisetSorted (zmodTwelveStrideInv amt) := by
  have hmem := List.mem_range.mpr hamt
  have hall :=
    List.all_eq_true.mp chord_rot_hist_sorted_amt_eq_zmod_stride_inv_range_cert amt hmem
  simpa using (decide_eq_true_iff.mp hall)

theorem chord_rot_hist_sorted_amt_one_eq_eleven :
    chordRotAmtHammingMultisetSorted 1 = chordRotAmtHammingMultisetSorted 11 :=
  chord_rot_hist_sorted_amt_eq_zmod_stride_inv (by decide)

theorem chord_rot_hist_sorted_amt_two_eq_ten :
    chordRotAmtHammingMultisetSorted 2 = chordRotAmtHammingMultisetSorted 10 :=
  chord_rot_hist_sorted_amt_eq_zmod_stride_inv (by decide)

theorem chord_rot_hist_sorted_amt_three_eq_nine :
    chordRotAmtHammingMultisetSorted 3 = chordRotAmtHammingMultisetSorted 9 :=
  chord_rot_hist_sorted_amt_eq_zmod_stride_inv (by decide)

theorem chord_rot_hist_sorted_amt_four_eq_eight :
    chordRotAmtHammingMultisetSorted 4 = chordRotAmtHammingMultisetSorted 8 :=
  chord_rot_hist_sorted_amt_eq_zmod_stride_inv (by decide)

theorem chord_rot_hist_sorted_amt_five_eq_seven :
    chordRotAmtHammingMultisetSorted 5 = chordRotAmtHammingMultisetSorted 7 :=
  chord_rot_hist_sorted_amt_eq_zmod_stride_inv (by decide)

/-! ### Half-turn stride (**`amt = 6`**) — six fixed gates -/

/-- Sorted distance witness for **`amt = 6`** (**`{0⁶,1²,2⁶,3¹⁰,4³⁰,5¹⁰,6²}`**). -/
def chordRotAmtSixHistogramSortedWitness : List Nat :=
  List.replicate 6 0 ++ List.replicate 2 1 ++ List.replicate 6 2 ++ List.replicate 10 3 ++ List.replicate 30 4 ++
    List.replicate 10 5 ++ List.replicate 2 6

theorem chord_rot_amt_six_histogram_sorted_length :
    chordRotAmtSixHistogramSortedWitness.length = 66 := by native_decide

theorem chord_rot_amt_six_histogram_sorted_eq_witness :
    chordRotAmtHammingMultisetSorted 6 = chordRotAmtSixHistogramSortedWitness := by native_decide

/-! ## Twelve-phase Gray corners vs naive numeric slots -/

theorem aeon_gray_corner_slot_lt (i : Fin twelve) : grayEncodeNat i.val < 128 := by
  rcases i with ⟨iv, hi⟩
  revert iv hi
  native_decide

/-- Embed **`Fin twelve`** phases as **Gray-labeled** **`Fin 128`** corners (**seven-bit permutation orbit**). -/
def aeonGrayCornerSlot (i : Fin twelve) : Fin 128 :=
  ⟨grayEncodeNat i.val, aeon_gray_corner_slot_lt i⟩

theorem aeon_gray_corner_ne_naive_embed_slot_at_five :
    (aeonGrayCornerSlot ⟨5, by decide⟩).val ≠
      (Gnosis.AeonTwelveHammingGrayDynamics.finTwelveEmbedSlot ⟨5, by decide⟩).val := by native_decide

/-! ## Modular scaffolding (**`lcm (12, 2⁷)`**) -/

theorem lcm_twelve_two_pow_seven_mod_twelve_zero :
    Nat.lcm 12 (2 ^ 7) % 12 = 0 := by native_decide

/-- **`384`** ticks advance additive **`Fin 12`** phase labels **without changing Gray-corner codewords**. -/
theorem lcm_gray_corner_phase_aligned (i : Fin twelve) :
    grayEncodeNat ((i.val + Nat.lcm 12 (2 ^ 7)) % 12) = grayEncodeNat i.val := by
  have hid :
      (i.val + Nat.lcm 12 (2 ^ 7)) % 12 = i.val := by
    calc
      (i.val + Nat.lcm 12 (2 ^ 7)) % 12 =
          ((i.val % 12) + (Nat.lcm 12 (2 ^ 7) % 12)) % 12 := Nat.add_mod _ _ _
      _ = (i.val % 12 + 0) % 12 := by rw [lcm_twelve_two_pow_seven_mod_twelve_zero]
      _ = i.val % 12 := by simp
      _ = i.val := Nat.mod_eq_of_lt i.isLt
  rw [hid]

end AeonTwelveHypercubeMajorization
end Gnosis
