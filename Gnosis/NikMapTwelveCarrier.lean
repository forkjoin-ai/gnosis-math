import Init
import Gnosis.AeonCycleTwelveShadow
import Gnosis.TwelveSlotSixtySixPairsCarrier

namespace Gnosis
namespace NikMapTwelveCarrier

/-!
# NIKA2 cosmological map ensemble: **12** maps, **66** cross-pairs (**combinatorial only**)

Bibliographic motivation (**Ponthieu, 2025**): the NIKA2 Cosmological Legacy Survey pipeline organizes deep-sky fields using
**twelve** parallel map products of the same sky regions; **excluding auto-correlations**, pairwise cross-comparisons induce
**`C(12,2) = 66`** distinct map pairs used to estimate cross-variance and characterize **confusion noise** in stacked mm-wave maps.

This Lean surface records **slot indices** and ascending **`Nat × Nat`** chords keyed to **`pairsIJ`** only --- **no** healpix
pixels, **no** transfer functions, **no** confusion-noise random field axioms. Astrophysical interpretation stays outside the kernel.

Formal spine: **`Gnosis.TwelveSlotSixtySixPairsCarrier`** (same **`pairsIJ`** skeleton as ecology-facing
**`Gnosis.EscherichiaColiOrthologTwelveCarrier`**).

Cross-links: **`Gnosis.SixtySixPairsAtlasWitness`**, **`Gnosis.AeonCycleTwelveShadow`**.
-/

open Gnosis.AeonCycleTwelveShadow
open Gnosis.TwelveSlotSixtySixPairsCarrier

/-- Twelve abstract map indices (**slots**, not healpix IDs). -/
abbrev MapSlotTwelve : Type :=
  TwelveSlot

/-- Strict ascending pair of map slots (**cross-map pair**, no auto-correlation). -/
abbrev OrderedMapStrictPair :=
  StrictAscendingPair

/-- Ascending **`Nat × Nat`** chord for a strict map pair (**cross-map slot**, no diagonal). -/
def OrderedMapStrictPair.toNatChord (p : OrderedMapStrictPair) : Nat × Nat :=
  StrictAscendingPair.toNatChord p

theorem OrderedMapStrictPair_mem_pairsIJ (p : OrderedMapStrictPair) :
    OrderedMapStrictPair.toNatChord p ∈ pairsIJ :=
  StrictAscendingPair.mem_pairsIJ p

/-- **`pairsIJ`** as the **66** cross-pair envelope (**unordered**, **`fst < snd`**). -/
def mapCrossPairSlotList : List (Nat × Nat) :=
  pairSlotList

theorem map_cross_pair_slot_list_length : mapCrossPairSlotList.length = 66 :=
  pair_slot_list_length

theorem exists_OrderedMapStrictPair_eq (q : Nat × Nat) (hq : q ∈ pairsIJ) :
    ∃ p : OrderedMapStrictPair, OrderedMapStrictPair.toNatChord p = q := by
  rcases exists_strict_ascending_pair_of_mem_pairsIJ q hq with ⟨p, hp⟩
  exact ⟨p, hp⟩

theorem OrderedMapStrictPair.toNatChord_injective :
    Function.Injective OrderedMapStrictPair.toNatChord := by
  intro p₁ p₂ hp
  exact StrictAscendingPair.toNatChord_injective hp

end NikMapTwelveCarrier
end Gnosis
