import Init
import Gnosis.AeonCycleTwelveShadow
import Gnosis.TwelveSlotSixtySixPairsCarrier

namespace Gnosis
namespace EscherichiaColiOrthologTwelveCarrier

/-!
# *Escherichia coli* group (**12** genomes): ortholog **pair-slot** carrier (**combinatorial only**)

Bibliographic motivation (**Konstantinidis et al., 2006**): comparative work on the *E. coli* group uses
**twelve** genome representatives and reports **66** nonredundant **unordered** ortholog pairings for whole-genome
distance summaries and intraspecies diversity bookkeeping.

This Lean surface models **indices and pair slots only** (Rustic Church): **no** nucleotide sequences,
**no** similarity scores, **no** homology oracle, **no** strain accession strings. Any identification with a concrete
genomics pipeline lives outside the proof kernel.

Formal spine: **`Gnosis.TwelveSlotSixtySixPairsCarrier`** (**shared **`pairsIJ`** envelope**).

## Carrier (names retained for stable imports)

* **`GenomeSlotTwelve`** — **`Fin twelve`** alias (**twelve** enumerated genome **slots**).
* **`OrderedOrthologStrictPair`** — two distinct slots **`lo < hi`** (val-level); maps to ascending **`Nat × Nat`** chords.
* **`orthologPairSlotList`** — synonym for **`AeonCycleTwelveShadow.pairsIJ`** (**66** unordered pair slots).

Every **`p ∈ pairsIJ`** arises from an **`OrderedOrthologStrictPair`** (**`exists_OrderedOrthologStrictPair_eq`**); **`toNatChord`** is injective (**`OrderedOrthologStrictPair.toNatChord_injective`**).

Cross-links: arithmetic atlas **`Gnosis.SixtySixPairsAtlasWitness`**, twelve-cycle geometry **`Gnosis.AeonCycleTwelveShadow`**,
cosmological twin **`Gnosis.NikMapTwelveCarrier`** (same combinatorial skeleton).
-/

open Gnosis.AeonCycleTwelveShadow
open Gnosis.TwelveSlotSixtySixPairsCarrier

/-- Twelve abstract genome indices (**slots**, **not** accessions). -/
abbrev GenomeSlotTwelve : Type :=
  TwelveSlot

/-- Unordered ortholog **pair slot** encoded as ascending **`Fin`** endpoints (**strict inequality**). -/
abbrev OrderedOrthologStrictPair :=
  StrictAscendingPair

/-- Embed strict **`Fin`** ortholog witness into ascending naturals mod **`twelve`**. -/
def OrderedOrthologStrictPair.toNatChord (p : OrderedOrthologStrictPair) : Nat × Nat :=
  StrictAscendingPair.toNatChord p

theorem OrderedOrthologStrictPair_mem_pairsIJ (p : OrderedOrthologStrictPair) :
    OrderedOrthologStrictPair.toNatChord p ∈ pairsIJ :=
  StrictAscendingPair.mem_pairsIJ p

/-- **`pairsIJ`** lists exactly the unordered ortholog pair-slot envelope used here. -/
def orthologPairSlotList : List (Nat × Nat) :=
  pairSlotList

theorem ortholog_pair_slot_list_length : orthologPairSlotList.length = 66 :=
  pair_slot_list_length

/-- Recover a genome-slot ortholog witness from any **`pairsIJ`** chord (**unique** up to proof irrelevance — injectivity below). -/
theorem exists_OrderedOrthologStrictPair_eq (q : Nat × Nat) (hq : q ∈ pairsIJ) :
    ∃ p : OrderedOrthologStrictPair, OrderedOrthologStrictPair.toNatChord p = q := by
  rcases exists_strict_ascending_pair_of_mem_pairsIJ q hq with ⟨p, hp⟩
  exact ⟨p, hp⟩

/-- **`OrderedOrthologStrictPair.toNatChord`** is injective (**distinct witnesses ⇒ distinct chords**). -/
theorem OrderedOrthologStrictPair.toNatChord_injective :
    Function.Injective OrderedOrthologStrictPair.toNatChord := by
  intro p₁ p₂ hp
  exact StrictAscendingPair.toNatChord_injective hp

end EscherichiaColiOrthologTwelveCarrier
end Gnosis
