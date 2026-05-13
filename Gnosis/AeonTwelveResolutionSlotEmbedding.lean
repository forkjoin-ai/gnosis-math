import Init
import Gnosis.AeonCycleTwelveShadow
import Gnosis.IupacResolutionCubeBound

namespace Gnosis
namespace AeonTwelveResolutionSlotEmbedding

/-!
# Twelve-cycle **`pairsIJ`** gates ↔ **`2^7`** IUPAC resolution slots

This module supplies **non-superficial** bridges:

1. **Concrete injective labeling.** Lexicographic rank on **`pairsIJ`** (**66** chords on **`ℤ/12ℤ`**),
   packaged as **`pairsIJLexRankCore`**, agrees list-wise with **`pairsIJ.idxOf`** (**kernel-checked**
   **`List.all`** certificates). On **`p ∈ pairsIJ`**, **`p.2 - (p.1 + 1)`** is well-behaved (**`pairsIJ_fst_lt_snd`**,
   **`Gnosis.AeonCycleTwelveShadow`**). Embedding **`Fin 118`** via **`chordGateAsIupacRow`** (first **`66`**
   atlas indices) and **`rowSlotFin128`** yields **`chordGateResolutionSlot`** --- distinct chords hit
   distinct **`2^7`** slots under the canonical IUPAC slot map.

2. **Algebraic obstruction.** **`¬ (12 ∣ 2^7)`** (**`twelve_not_dvd_two_pow_seven`**): by Lagrange,
   **`ℤ/128ℤ`** has only **`2`**-power subgroup orders, so **no** subgroup has order **`12`** --- hence
   **no** injective homomorphism **`ℤ/12ℤ → ℤ/128ℤ`** whose image is an additive subgroup (phase-linear
   alignment between **`mod 12`** deck ticks and **`mod 128`** translation is impossible without collapsing).

3. **Synchronization modulus.** **`gcd (12, 2^7) = 4`** and **`lcm (12, 2^7) = 384`** locate the joint
   period when independent **`mod 12`** and **`mod 128`** counters realign.

Khovanov **`{0,1}^7`** bookkeeping still differs categorically from **`rotPairNatAdd`** (**`Gnosis.AeonTwelveCarrierList`**):
here **set-theoretic slot injections are compatible**, **homomorphic clocks are not**.

Zero `sorry`, zero new `axiom`.
-/

open Gnosis.AeonCycleTwelveShadow
open Gnosis.IupacResolutionCubeBound

/-- Cardinality of pairs listed **before** first coordinate **`i`** in lex **`pairsIJ`** order.

Formula **`∑_{t < i} (11 - t) = i · 11 - (i - 1) · i / 2`** for **`i ≥ 1`** (`pairsIJLexPrefixBefore 0 = 0`). -/
def pairsIJLexPrefixBefore (i : Nat) : Nat :=
  match i with
  | 0 => 0
  | Nat.succ i' =>
      let i := Nat.succ i'
      i * 11 - i' * i / 2

/-- Closed lex rank (**no hypothesis**) --- agrees with **`pairsIJ.idxOf`** on **`pairsIJ`**. -/
def pairsIJLexRankCore (p : Nat × Nat) : Nat :=
  pairsIJLexPrefixBefore p.1 + (p.2 - (p.1 + 1))

/-- Gate rank (**membership bundles** the **`pairsIJ`** carrier only); definitionally **`pairsIJLexRankCore`**. -/
def pairsIJLexRank (p : Nat × Nat) (_hp : p ∈ pairsIJ) : Nat :=
  pairsIJLexRankCore p

/-! ### Finite **`native_decide`** certificates (`List.all`)

See **`List.all_eq_true`** (**`Init`**): nested **`all`** unfolds to **`∀ · ∈ pairsIJ, ∀ · ∈ pairsIJ, …`**.
-/

private theorem pairsIJ_lex_rank_core_eq_idxOf_all :
    pairsIJ.all (fun p => decide (pairsIJLexRankCore p = pairsIJ.idxOf p)) = true := by native_decide

private theorem pairsIJ_idx_inj_nested :
    pairsIJ.all (fun p =>
        pairsIJ.all (fun q =>
          decide (pairsIJ.idxOf p = pairsIJ.idxOf q → p = q))) = true := by native_decide

private theorem pairsIJ_idx_lt_all :
    pairsIJ.all (fun p => decide (pairsIJ.idxOf p < 66)) = true := by native_decide

theorem pairsIJ_lex_rank_core_eq_idxOf (p : Nat × Nat) (hp : p ∈ pairsIJ) :
    pairsIJLexRankCore p = pairsIJ.idxOf p := by
  have hall := List.all_eq_true.mp pairsIJ_lex_rank_core_eq_idxOf_all p hp
  simpa using hall

theorem forall_mem_pairs_ij_idx_inj {p q : Nat × Nat} (hp : p ∈ pairsIJ) (hq : q ∈ pairsIJ)
    (hr : pairsIJ.idxOf p = pairsIJ.idxOf q) : p = q := by
  have houter := List.all_eq_true.mp pairsIJ_idx_inj_nested p hp
  have hinner := List.all_eq_true.mp houter q hq
  exact (decide_eq_true_iff.mp hinner) hr

theorem pairsIJ_lex_rank_lt_sixty_six (p : Nat × Nat) (hp : p ∈ pairsIJ) :
    pairsIJLexRank p hp < 66 := by
  dsimp [pairsIJLexRank]
  rw [pairsIJ_lex_rank_core_eq_idxOf p hp]
  have hall := List.all_eq_true.mp pairsIJ_idx_lt_all p hp
  simpa using hall

theorem pairsIJ_lex_rank_injective {p q : Nat × Nat} (hp : p ∈ pairsIJ) (hq : q ∈ pairsIJ)
    (hr : pairsIJLexRank p hp = pairsIJLexRank q hq) : p = q := by
  dsimp [pairsIJLexRank] at hr
  rw [pairsIJ_lex_rank_core_eq_idxOf p hp, pairsIJ_lex_rank_core_eq_idxOf q hq] at hr
  exact forall_mem_pairs_ij_idx_inj hp hq hr

/-- Embed a **`pairsIJ`** gate as an IUPAC row index (**first **`66`** rows**). -/
def chordGateAsIupacRow (p : Nat × Nat) (hp : p ∈ pairsIJ) : Fin 118 :=
  ⟨pairsIJLexRank p hp,
    Nat.lt_trans (pairsIJ_lex_rank_lt_sixty_six p hp) sixty_six_lt_iupac_row_count⟩

theorem chordGateAsIupacRow_injective {p q : Nat × Nat} (hp : p ∈ pairsIJ) (hq : q ∈ pairsIJ)
    (h : chordGateAsIupacRow p hp = chordGateAsIupacRow q hq) : p = q := by
  refine pairsIJ_lex_rank_injective hp hq ?_
  simpa [chordGateAsIupacRow] using congrArg Fin.val h

/-- Compose with **`rowSlotFin128`**: chord gates land on **`66`** distinct **`2^7`** slots (**prefix rows**). -/
def chordGateResolutionSlot (p : Nat × Nat) (hp : p ∈ pairsIJ) : Fin 128 :=
  rowSlotFin128 (chordGateAsIupacRow p hp)

theorem chordGateResolutionSlot_inj {p q : Nat × Nat} (hp : p ∈ pairsIJ) (hq : q ∈ pairsIJ)
    (h : chordGateResolutionSlot p hp = chordGateResolutionSlot q hq) : p = q :=
  chordGateAsIupacRow_injective hp hq (rowSlotFin128_injective h)

/-! ## Algebraic obstruction (**Lagrange** on **`ℤ/128ℤ`**)-/

theorem twelve_not_dvd_two_pow_seven : ¬12 ∣ 2 ^ 7 := by native_decide

/-! ### Interpretation

Any injective homomorphism **`ℤ/12ℤ → ℤ/128ℤ`** (additive groups) would embed **`ℤ/12ℤ`** as a subgroup of
order **`12`**. Subgroups of **`ℤ/128ℤ`** have order dividing **`128`**, hence a power of **`2`**; **`12`**
is not such a divisor (**`twelve_not_dvd_two_pow_seven`**), so **no** such embedding exists for
**subgroup-valued** phase arithmetic.

The slot map **`chordGateResolutionSlot`** is **not** claimed to intertwine **`+ mod 12`** with **`+ mod 128`**.
-/

/-! ## **`gcd` / `lcm`** envelope-/

theorem gcd_twelve_two_pow_seven_eq_four : Nat.gcd 12 (2 ^ 7) = 4 := by native_decide

theorem lcm_twelve_two_pow_seven_eq_three_eighty_four : Nat.lcm 12 (2 ^ 7) = 384 := by native_decide

end AeonTwelveResolutionSlotEmbedding
end Gnosis
