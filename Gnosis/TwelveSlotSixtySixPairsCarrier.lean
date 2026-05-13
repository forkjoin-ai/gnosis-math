import Init
import Gnosis.AeonCycleTwelveShadow

namespace Gnosis
namespace TwelveSlotSixtySixPairsCarrier

/-!
# Twelve slots, sixty-six strict pairs (**combinatorial carrier only**)

Neutral **`Fin twelve`** slots and ascending unordered **`Nat × Nat`** chords aligned with
**`Gnosis.AeonCycleTwelveShadow.pairsIJ`** (**length `66`**).

This module is the **shared formal spine**: **`C(12,2)`** unordered pairs with **`fst < snd`** and endpoints in
**`0 … eleven`**. Domain metaphors (genomics, cosmological map ensembles, etc.) live in thin wrappers that import here;
Lean carries **indices only** --- **no** sequences, **no** pixels, **no** noise-model axioms (Rustic Church).

Cross-links: **`Gnosis.AeonCycleTwelveShadow`** (**`pairsIJ`**, **`pairsIJ_length`**),
**`Gnosis.TwelveSlotSixtySixPairsCyclicShear`** (**`rotateTwelveSlot`**, **`StrictAscendingPair.rotatePairStep`** / **`rotatePairIterate`**),
**`Gnosis.SixtySixPairsAtlasWitness`** (bibliographic atlas paragraph).
-/

open Gnosis.AeonCycleTwelveShadow

/-- Twelve labeled slots (**abstract indices**). -/
abbrev TwelveSlot : Type :=
  Fin twelve

/-- Strict ascending pair of slots (**unordered chord**, **`lo < hi`** at **`val`** level). -/
structure StrictAscendingPair where
  lo : TwelveSlot
  hi : TwelveSlot
  hlt : lo.val < hi.val

/-- Embed a strict pair into ascending naturals (**both coordinates `< twelve`**). -/
def StrictAscendingPair.toNatChord (p : StrictAscendingPair) : Nat × Nat :=
  (p.lo.val, p.hi.val)

theorem StrictAscendingPair.mem_pairsIJ (p : StrictAscendingPair) :
    p.toNatChord ∈ pairsIJ :=
  (pair_mem_pairsIJ_iff_fst_lt_snd p.lo.val p.hi.val p.lo.isLt p.hi.isLt).mpr p.hlt

/-- Synonym for **`pairsIJ`** (**66** rows). -/
def pairSlotList : List (Nat × Nat) :=
  pairsIJ

theorem pair_slot_list_length : pairSlotList.length = 66 :=
  pairsIJ_length

/-- Recover a strict pair witness from any **`pairsIJ`** chord. -/
theorem exists_strict_ascending_pair_of_mem_pairsIJ (q : Nat × Nat) (hq : q ∈ pairsIJ) :
    ∃ p : StrictAscendingPair, p.toNatChord = q := by
  rcases pairsIJ_coords_lt_twelve q hq with ⟨h₁, h₂⟩
  refine ⟨{ lo := ⟨q.1, h₁⟩, hi := ⟨q.2, h₂⟩, hlt := ?_ }, ?_⟩
  · exact (pair_mem_pairsIJ_iff_fst_lt_snd q.1 q.2 h₁ h₂).1 hq
  · rfl

theorem StrictAscendingPair.toNatChord_injective :
    Function.Injective StrictAscendingPair.toNatChord := by
  rintro ⟨lo₁, hi₁, _⟩ ⟨lo₂, hi₂, _⟩ hpq
  simp only [StrictAscendingPair.toNatChord, Prod.mk.injEq] at hpq
  rcases hpq with ⟨hl, hh⟩
  have elo : lo₁ = lo₂ := Fin.ext hl
  have ehi : hi₁ = hi₂ := Fin.ext hh
  subst elo
  subst ehi
  rfl

end TwelveSlotSixtySixPairsCarrier
end Gnosis
