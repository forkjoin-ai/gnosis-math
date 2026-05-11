/-
  PleromaticResidualAtlas.lean
  ============================

  Pins the structural invariants of the Pleromatic Residual Atlas:
  BWMR capture records, BWDC dictionary blobs, and the dict-mode
  encode contract.

  Imports Init + the bitwise wire contract. Zero `sorry`, zero new
  `axiom`.
-/

import Init
import Gnosis.AmplituhedronWireBitwiseContract

namespace PleromaticResidualAtlas

open AmplituhedronWireBitwiseContract

/-! ## BWMR capture record format

  Each captured residual is appended as a fixed-header record:
    u16 layer_idx | u32 seq_idx | u32 hidden_dim | u64 timestamp_ms | f32[hidden_dim]

  Header width = 2 + 4 + 4 + 8 = 18 bytes.
  Payload width = 4 * hidden_dim bytes.
-/

def bwmrHeaderLen : Nat := 18

theorem bwmr_header_len_oracle : bwmrHeaderLen = 18 := by
  unfold bwmrHeaderLen; decide

/-- Total record length given a hidden dimension. -/
def bwmrRecordLen (hidden_dim : Nat) : Nat := bwmrHeaderLen + 4 * hidden_dim

theorem bwmr_record_len_qwen_7b :
    bwmrRecordLen 3584 = 14354 := by
  unfold bwmrRecordLen bwmrHeaderLen; decide

/-! ## BWDC dictionary format

  Magic `BWDC` (4 bytes: [0x42, 0x57, 0x44, 0x43]) + u32 version (1)
  + u32 entry_count + u32 entry_len + entry_count * entry_len bytes.

  Header width = 4 + 4 + 4 + 4 = 16 bytes.
-/

def bwdcMagicBytes : List Nat := [0x42, 0x57, 0x44, 0x43]
def bwdcVersion : Nat := 1
def bwdcHeaderLen : Nat := 16

theorem bwdc_magic_oracle :
    bwdcMagicBytes = [66, 87, 68, 67] := by
  unfold bwdcMagicBytes; decide

theorem bwdc_version_oracle : bwdcVersion = 1 := by
  unfold bwdcVersion; decide

theorem bwdc_header_len_oracle : bwdcHeaderLen = 16 := by
  unfold bwdcHeaderLen; decide

def bwdcTotalLen (entry_count entry_len : Nat) : Nat :=
  bwdcHeaderLen + entry_count * entry_len

theorem bwdc_total_len_4k_64 :
    bwdcTotalLen 4096 64 = 262160 := by
  unfold bwdcTotalLen bwdcHeaderLen; decide

/-! ## Dict-mode encode contract

  When a dictionary is loaded (GNOSIS_RESIDUAL_DICT env), residual
  encoding routes through `bw_codec::encode_bw` with the dictionary
  in `EncodeBwOptions`. The version byte of the resulting .bw blob
  has the DICT_FLAG bit set (0x80).

  When no dictionary is loaded, version byte is plain (no flag bits).
-/

def dictFlagSet (version_byte : Nat) : Bool :=
  (version_byte &&& 0x80) ≠ 0

theorem dict_flag_set_when_high_bit :
    dictFlagSet 0x81 = true := by
  unfold dictFlagSet; decide

theorem dict_flag_clear_when_low_bit :
    dictFlagSet 0x01 = false := by
  unfold dictFlagSet; decide

/-! ## Bundled pentad -/

theorem pleromatic_residual_atlas_pentad :
    bwmrHeaderLen = 18 ∧
    bwmrRecordLen 3584 = 14354 ∧
    bwdcMagicBytes = [66, 87, 68, 67] ∧
    bwdcVersion = 1 ∧
    bwdcHeaderLen = 16 :=
  ⟨bwmr_header_len_oracle, bwmr_record_len_qwen_7b,
   bwdc_magic_oracle, bwdc_version_oracle, bwdc_header_len_oracle⟩

end PleromaticResidualAtlas
