import Init
import Gnosis.AeonCycleTwelveShadow
import Gnosis.AeonTwelveCarrierList
import Gnosis.AeonTwelveResolutionSlotEmbedding

namespace Gnosis
namespace AeonTwelveHammingGrayDynamics

/-!
# Hamming / Gray **`{0,1}^7`** dynamics vs twelve-cycle rotations (**not intertwined**)

This module compares three concrete clocks on **`Fin 128`** **indices** (seven-bit masks):

1. **Hamming distance** on **`128 = 2^7`** slots (**`fin128HammingDist`**): XOR population count on the low **`7`** bits.

2. **Binary-reflected Gray adjacency** along the usual **`k ↦ k+1`** binary counter (**`grayEncodeNat`**):
   successive Gray codewords differ in exactly **one** bit (**`gray_binary_succ_adjacent`**).

3. **Twelve-phase stepping**: **`cyclicSucc`** on **`Fin 12`** vertices embedded into **`Fin 128`** by their numeric labels,
   and **`rotPairNatAdd 1`** (**sorted **`pairsIJ`** carrier**, not column **`rotatePluckerLabel`** --- **`Gnosis.AeonCycleTwelveShadow`**, module doc **Rotation chart**) shears on **`pairsIJ`** chord gates lifted through **`chordGateResolutionSlot`**.

**Takeaway.** Gray's **`127`** primitive edges along that Hamiltonian Gray walk are **unit Hamming**. One **`rotPairNatAdd 1`**
tick from the pivot chord **`(0,1)`** jumps **`chordGateResolutionSlot`** by **`11`** slots (**not unit Hamming**), even though both maps live on **`Fin 128`** indices.

Joint **`mod 12`** vs **`mod 128`** periodicity stays **`lcm = 384`** (**`Gnosis.AeonTwelveResolutionSlotEmbedding`**).

**Majorization layer (**full **`66`**-gate shear census, Gray permutation / decode inverse, Gray-corner lifts**) —
**`Gnosis.AeonTwelveHypercubeMajorization`**.

Zero `sorry`, zero new `axiom`.
-/

open Gnosis.AeonCycleTwelveShadow
open Gnosis.AeonTwelveCarrierList
open Gnosis.AeonTwelveResolutionSlotEmbedding
open Gnosis.DiscreteClosedTimelikeStep

/-- Population count on the lowest **`width`** bits (**length-`width` hypercube Hamming weight**). -/
def hammingWtLowBits (x : Nat) (width : Nat) : Nat :=
  (List.range width).foldl (fun acc i => acc + if x.testBit i then 1 else 0) 0

/-- Hamming distance between **`Fin 128`** indices (**seven-bit XOR mass**). -/
def fin128HammingDist (u v : Fin 128) : Nat :=
  hammingWtLowBits (u.val ^^^ v.val) 7

theorem fin128HammingDist_symm (u v : Fin 128) :
    fin128HammingDist u v = fin128HammingDist v u := by
  simp [fin128HammingDist, Nat.xor_comm]

/-- Standard binary-reflected Gray map **`x ↦ x XOR (x >>> 1)`** at **`Nat`** precision (truncate externally). -/
def grayEncodeNat (x : Nat) : Nat :=
  x ^^^ Nat.shiftRight x 1

/-! ### Gray walk: **`k`** vs **`k+1`** are adjacent hypercube edges -/

private theorem gray_binary_succ_adjacent_cert :
    (List.range 127).all (fun k =>
      decide (hammingWtLowBits (grayEncodeNat k ^^^ grayEncodeNat (k + 1)) 7 = 1)) = true := by native_decide

/-- Along **`k ↦ k + 1`** (**`k < 127`**), Gray codewords differ by Hamming weight **`1`** (**Hamiltonian Gray-list edge**). -/
theorem gray_binary_succ_adjacent (k : Nat) (hk : k < 127) :
    hammingWtLowBits (grayEncodeNat k ^^^ grayEncodeNat (k + 1)) 7 = 1 := by
  have hall := List.all_eq_true.mp gray_binary_succ_adjacent_cert k (List.mem_range.mpr hk)
  simpa using hall

/-! ### Twelve-cycle vertex step can flip **many** bits at once (embedded labels)-/

/-- Embedding **`Fin twelve → Fin 128`** by the canonical numeric tag (**coercion**, **`128`** ceiling automatic). -/
def finTwelveEmbedSlot (i : Fin twelve) : Fin 128 :=
  ⟨i.val, Nat.lt_trans i.isLt (by decide : 12 < 128)⟩

theorem cyclic_wrap_vertex_xor_mass_eq_three_embedded :
    hammingWtLowBits
        ((finTwelveEmbedSlot ⟨11, by decide⟩).val ^^^ (finTwelveEmbedSlot (cyclicSucc h12 ⟨11, by decide⟩)).val)
        7 =
      3 := by
  native_decide

theorem exists_cyclic_vertex_embed_not_unit_hamming :
    ∃ i : Fin twelve,
      hammingWtLowBits ((finTwelveEmbedSlot i).val ^^^ (finTwelveEmbedSlot (cyclicSucc h12 i)).val) 7 ≠ 1 := by
  refine ⟨⟨11, by decide⟩, ?_⟩
  rw [cyclic_wrap_vertex_xor_mass_eq_three_embedded]
  decide

/-! ### **`rotPairNatAdd`** through **`chordGateResolutionSlot`** breaks Gray-edge thickness -/

theorem pairsIJ_mem_edge_01 : (0, 1) ∈ pairsIJ :=
  pairsIJ_mem_axis_pair_01

theorem pairsIJ_mem_edge_12 : (1, 2) ∈ pairsIJ :=
  pairsIJ_mem_consecutive 1 (by decide)

theorem rot_pair_nat_add_one_axis_pairs01_eq_edge12 :
    rotPairNatAdd 1 (0, 1) = (1, 2) := by native_decide

theorem chord_gate_slots_axis_vs_rot_mass_three :
    hammingWtLowBits
        ((chordGateResolutionSlot (0, 1) pairsIJ_mem_edge_01).val ^^^
          (chordGateResolutionSlot (1, 2) pairsIJ_mem_edge_12).val)
        7 =
      3 := by native_decide

/-- Pivot **`+1`** shear moves **`(0,1) ↦ (1,2)`**, but canonical **`rowSlotFin128`** indices **`0`** vs **`11`** differ in **`3`** bits. -/
theorem chord_rot_axis_gate_not_gray_neighbor :
    fin128HammingDist (chordGateResolutionSlot (0, 1) pairsIJ_mem_edge_01)
        (chordGateResolutionSlot (1, 2) pairsIJ_mem_edge_12) ≠ 1 := by
  have h₃ := chord_gate_slots_axis_vs_rot_mass_three
  dsimp [fin128HammingDist] at h₃ ⊢
  rw [h₃]
  decide

/-! ### Joint period reminder (**`384`**)-/

theorem lcm_twelve_two_pow_seven_eq_three_eighty_four :
    Nat.lcm 12 (2 ^ 7) = 384 :=
  Gnosis.AeonTwelveResolutionSlotEmbedding.lcm_twelve_two_pow_seven_eq_three_eighty_four

end AeonTwelveHammingGrayDynamics
end Gnosis
