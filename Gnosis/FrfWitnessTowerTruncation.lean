import Gnosis.FrfWitnessTower
import Gnosis.FrfInherentGestalt

/-!
# Tower truncation / prefix splits for homomorphism merges

**Purpose.** Formal packaging for “sideways quantization” narratives: any finite digit stream splits into a
**head** (`List.take k`) and **tail** (`List.drop k`). Because `triadMerge` and `xorMerge` are monoid folds
over concatenation (`triad_merge_append`, `xorMerge_append`), the merged residue of the full stream is a
**deterministic recombination** of head and tail summaries — not order‑oblivious magic, but exact bookkeeping.

This does **not** assert approximation bounds on floating‑point weights or neural logits; it only pins the
**algebraic interface** where a compressor may retain `(triadMerge head, triadMerge tail)` instead of raw digits.

**Relation to non‑injectivity.** Full‑stream `triadMerge` remains many‑to‑one (`triad_merge_not_injective`);
truncation certificates carry **two** coarse residues, not a unique preimage.

Zero `sorry`.
-/

namespace Gnosis
namespace FrfWitnessTowerTruncation

open FrfWitnessTower
open FrfInherentGestalt

/-! ## Split lemmas (`take` / `drop`) -/

theorem triad_merge_take_drop_split (ds : List (Fin 3)) (k : Nat) :
    triadMerge ds =
      triadAdd (triadMerge (List.take k ds)) (triadMerge (List.drop k ds)) := by
  calc
    triadMerge ds =
      triadMerge (List.take k ds ++ List.drop k ds) :=
        congrArg triadMerge (Eq.symm (List.take_append_drop k ds))
    _ = triadAdd (triadMerge (List.take k ds)) (triadMerge (List.drop k ds)) :=
          triad_merge_append _ _

theorem xor_merge_take_drop_split (bs : List Bool) (k : Nat) :
    xorMerge bs =
      (xorMerge (List.take k bs)).xor (xorMerge (List.drop k bs)) := by
  calc
    xorMerge bs =
      xorMerge (List.take k bs ++ List.drop k bs) :=
        congrArg xorMerge (Eq.symm (List.take_append_drop k bs))
    _ = (xorMerge (List.take k bs)).xor (xorMerge (List.drop k bs)) :=
          xorMerge_append _ _

/-! ## Parity track splits commute with `map finThreeParityBit` -/

theorem map_finThreeParityBit_take_drop (ds : List (Fin 3)) (k : Nat) :
    List.map finThreeParityBit ds =
      List.map finThreeParityBit (List.take k ds) ++
        List.map finThreeParityBit (List.drop k ds) := by
  calc
    List.map finThreeParityBit ds =
      List.map finThreeParityBit (List.take k ds ++ List.drop k ds) :=
        congrArg (List.map finThreeParityBit) (Eq.symm (List.take_append_drop k ds))
    _ = List.map finThreeParityBit (List.take k ds) ++ List.map finThreeParityBit (List.drop k ds) := by
          rw [List.map_append]

theorem xor_parity_track_take_drop_split (ds : List (Fin 3)) (k : Nat) :
    xorMerge (List.map finThreeParityBit ds) =
      (xorMerge (List.map finThreeParityBit (List.take k ds))).xor
        (xorMerge (List.map finThreeParityBit (List.drop k ds))) := by
  simpa [List.map_take, List.map_drop] using xor_merge_take_drop_split (List.map finThreeParityBit ds) k

/-! ## Bundled certificate (single citation block) -/

theorem braid_quotient_take_drop_certificate (ds : List (Fin 3)) (bs : List Bool) (k : Nat) (k' : Nat) :
    triadMerge ds =
        triadAdd (triadMerge (List.take k ds)) (triadMerge (List.drop k ds)) ∧
      xorMerge bs =
        (xorMerge (List.take k' bs)).xor (xorMerge (List.drop k' bs)) ∧
      xorMerge (List.map finThreeParityBit ds) =
        (xorMerge (List.map finThreeParityBit (List.take k ds))).xor
          (xorMerge (List.map finThreeParityBit (List.drop k ds))) :=
  ⟨triad_merge_take_drop_split ds k,
    xor_merge_take_drop_split bs k',
    xor_parity_track_take_drop_split ds k⟩

end FrfWitnessTowerTruncation
end Gnosis
