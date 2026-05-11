/-
  Death5CrossPrefixCompression.lean
  =================================

  Death #5 — Cross-Prefix Compression via Pleromatic Dictionary Encoding.

  ## The unifying observation

  Death #1 (MatVecMemo) caches per-matmul. Death #2 (Amplituhedron)
  caches exact-prefix prefills. Death #3 (aeon-flow) reduces per-hop
  framing. Death #4 (Pair X) overlaps adjacent layers. Each prior
  Death caches at a different granularity.

  Death #5 caches REUSABLE BYTE PATTERNS across non-identical
  prefixes, via bw-codec dict-mode learned from production
  Luminary-basin residual traffic. The dictionary is the cache; the
  cache is consulted via dict-mode encode/decode rather than a hash
  lookup, so partial pattern matches compose with whatever payload
  surrounds them.

  ## Composition with prior Deaths

  - Death #2 hits on EXACT prefix; Death #5 hits on PARTIAL byte
    patterns. They compose: Death #2 takes the exact-match prefill;
    Death #5 takes whatever residual segments match dictionary
    entries.
  - Death #1 (MatVecMemo) caches matmul outputs intra-layer; Death
    #5 compresses inter-layer wire transport. Orthogonal.
  - Death #3 (aeon-flow) reduces framing per hop; Death #5 reduces
    the bytes that flow through the framing. Orthogonal.
  - Death #4 (Pair X) overlaps the layer chain; Death #5 reduces
    the bytes of each layer's tail residual. Orthogonal.

  Imports Init + AmplituhedronWireBitwiseContract + PleromaticResidualAtlas.
  Zero `sorry`, zero new `axiom`.
-/

import Init
import Gnosis.AmplituhedronWireBitwiseContract
import Gnosis.PleromaticResidualAtlas

namespace Death5CrossPrefixCompression

open AmplituhedronWireBitwiseContract
open PleromaticResidualAtlas

/-! ## The five Deaths catalog -/

inductive Death where
  | matVecMemo            -- #1 — SHIPPED
  | amplituhedronVolume   -- #2 — SHIPPED
  | aeonFlowFraming       -- #3 — IN-FLIGHT
  | octonionFano          -- #4 — IN-FLIGHT
  | crossPrefixCompress   -- #5 — THIS MODULE
  deriving DecidableEq, Repr

def deathNumber : Death → Nat
  | .matVecMemo          => 1
  | .amplituhedronVolume => 2
  | .aeonFlowFraming     => 3
  | .octonionFano        => 4
  | .crossPrefixCompress => 5

theorem death5_is_five : deathNumber Death.crossPrefixCompress = 5 := by
  unfold deathNumber; decide

/-! ## Death #5's claim

Each Death has a claim. Death #5's claim: the per-replay wire payload
shrinks by a factor strictly greater than 1 when a non-empty
dictionary is loaded, on payloads whose byte patterns intersect the
dictionary entries.

The Lean side pins the STRUCTURAL invariants: dictionary presence
implies DICT_FLAG set on the bw-codec version byte; absence implies
flag clear. The shrink factor is empirical and lives in the protocol
doc, not Lean. -/

/-- A Death #5 wire emission carries a flag bit indicating whether
    the dictionary was used. -/
inductive DictUsage where
  | usedDictionary
  | plainBwCodec
  deriving DecidableEq, Repr

/-- The bw-codec version byte under dict-mode has the DICT_FLAG bit
    set (0x80). Plain encode clears all flag bits. -/
def versionByteOf (u : DictUsage) : Nat :=
  match u with
  | .usedDictionary => 0x81   -- BW_VERSION 0x01 + DICT_FLAG 0x80
  | .plainBwCodec   => 0x01   -- BW_VERSION 0x01

theorem version_byte_with_dict_has_flag :
    dictFlagSet (versionByteOf DictUsage.usedDictionary) = true := by
  unfold versionByteOf; exact dict_flag_set_when_high_bit

theorem version_byte_without_dict_has_no_flag :
    dictFlagSet (versionByteOf DictUsage.plainBwCodec) = false := by
  unfold versionByteOf; exact dict_flag_clear_when_low_bit

/-! ## Composition table — orthogonality with prior Deaths

Each entry pins that Death #5's key space is disjoint from the prior
Deaths' key spaces. Composition is multiplicative on throughput. -/

/-- Key spaces. Death #5 keys on dictionary-entry indices; Death #2
    keys on prefix hashes; Death #1 keys on (W, x) matmul tuples;
    Deaths #3 and #4 don't cache (they transform wire/timing). -/
inductive KeySpace where
  | dictionaryEntryIndex   -- #5
  | prefixHash             -- #2
  | matVecBucket           -- #1
  | none                   -- #3 / #4 — transform, not cache
  deriving DecidableEq, Repr

def deathKeySpace : Death → KeySpace
  | .matVecMemo          => .matVecBucket
  | .amplituhedronVolume => .prefixHash
  | .aeonFlowFraming     => .none
  | .octonionFano        => .none
  | .crossPrefixCompress => .dictionaryEntryIndex

theorem death5_key_disjoint_from_death2 :
    deathKeySpace Death.crossPrefixCompress ≠ deathKeySpace Death.amplituhedronVolume := by
  unfold deathKeySpace; decide

theorem death5_key_disjoint_from_death1 :
    deathKeySpace Death.crossPrefixCompress ≠ deathKeySpace Death.matVecMemo := by
  unfold deathKeySpace; decide

/-! ## Bundled pentad -/

theorem death5_cross_prefix_compression_pentad :
    deathNumber Death.crossPrefixCompress = 5 ∧
    dictFlagSet (versionByteOf DictUsage.usedDictionary) = true ∧
    dictFlagSet (versionByteOf DictUsage.plainBwCodec) = false ∧
    deathKeySpace Death.crossPrefixCompress ≠ deathKeySpace Death.amplituhedronVolume ∧
    deathKeySpace Death.crossPrefixCompress ≠ deathKeySpace Death.matVecMemo :=
  ⟨death5_is_five,
   version_byte_with_dict_has_flag,
   version_byte_without_dict_has_no_flag,
   death5_key_disjoint_from_death2,
   death5_key_disjoint_from_death1⟩

end Death5CrossPrefixCompression
