import Init
import Gnosis.AmplituhedronWireBitwiseContract

/-
  PositionalDictModeContract.lean
  ===============================

  Pins the positional dict-mode wire format invariants for bw_codec.
  Mirrors the canonical *_runtime_oracle_* pentad pattern.

  POSDICT mode is a Rust-native dict semantics: dictionary entries
  are a positional list; encoder substitutes matching windows with a
  sentinel + u32 LE index; decoder takes the same list to invert.
  Distinct from the TS-native DICT_FLAG (0x80) parity-sink semantics.

  Imports Init + AmplituhedronWireBitwiseContract. Zero `sorry`,
  zero new `axiom`.
-/


namespace PositionalDictModeContract

open AmplituhedronWireBitwiseContract

/-! ## The new flag bit -/

/-- Bit 5 of the bw-codec version byte. Distinct from
    `BW_VERSION_DICT_FLAG = 0x80` (parity-sink) and
    `BW_VERSION_LIFT_FLAG = 0x40` (lift). -/
def posdictFlag : Nat := 0x20

theorem posdict_flag_oracle :
    posdictFlag = 32 := by
  unfold posdictFlag; decide

/-- Version byte under POSDICT mode: base version 0x01 ORed with
    posdict flag 0x20 = 0x21. -/
def posdictVersionByte : Nat := 0x01 ||| 0x20

theorem posdict_version_byte_oracle :
    posdictVersionByte = 0x21 := by
  unfold posdictVersionByte; decide

/-- Flag-bit check: a version byte has POSDICT set iff bit 5 is on. -/
def hasPosdictFlag (version_byte : Nat) : Bool :=
  (version_byte &&& posdictFlag) ≠ 0

theorem has_posdict_flag_set :
    hasPosdictFlag 0x21 = true := by
  unfold hasPosdictFlag posdictFlag; decide

theorem has_posdict_flag_clear :
    hasPosdictFlag 0x01 = false := by
  unfold hasPosdictFlag posdictFlag; decide

/-! ## POSDICT and DICT flags are mutually exclusive in this protocol

The encoder MUST NOT set both POSDICT_FLAG (0x20) and DICT_FLAG (0x80)
on the same wire blob — the two dict semantics are mutually exclusive.
This is a structural invariant the runtime must satisfy. -/

def hasDictFlag (version_byte : Nat) : Bool :=
  (version_byte &&& 0x80) ≠ 0

/-- A valid POSDICT wire has POSDICT_FLAG set AND DICT_FLAG clear. -/
def IsValidPosdictWire (version_byte : Nat) : Bool :=
  hasPosdictFlag version_byte && !hasDictFlag version_byte

theorem valid_posdict_wire_0x21 :
    IsValidPosdictWire 0x21 = true := by
  unfold IsValidPosdictWire hasPosdictFlag hasDictFlag posdictFlag; decide

theorem invalid_posdict_wire_when_dict_also_set :
    IsValidPosdictWire 0xA1 = false := by
  unfold IsValidPosdictWire hasPosdictFlag hasDictFlag posdictFlag; decide

/-! ## Header lengths

POSDICT wire layout (mirrors the Rust + TS implementations):
  magic (4) + version (1) + mime_code (1) + fp48 (6)
  + u32 LE orig_len (4) + u32 LE enc_len (4) + payload[enc_len]

Header (everything before payload) = 4 + 1 + 1 + 6 + 4 + 4 = 20 bytes. -/

def posdictHeaderLen : Nat := 20

theorem posdict_header_len_oracle :
    posdictHeaderLen = 20 := by
  unfold posdictHeaderLen; decide

/-! ## Match sentinel byte

The encoder substitutes matching windows with `0xFF + u32 LE index`.
Literal `0xFF` bytes are escaped as `0xFF 0xFF`. -/

def posdictMatchSentinel : Nat := 0xFF

theorem posdict_match_sentinel_oracle :
    posdictMatchSentinel = 255 := by
  unfold posdictMatchSentinel; decide

/-! ## Bundled pentad -/

theorem positional_dict_mode_pentad :
    posdictFlag = 32 ∧
    posdictVersionByte = 0x21 ∧
    hasPosdictFlag 0x21 = true ∧
    posdictHeaderLen = 20 ∧
    posdictMatchSentinel = 255 :=
  ⟨posdict_flag_oracle, posdict_version_byte_oracle,
   has_posdict_flag_set, posdict_header_len_oracle, posdict_match_sentinel_oracle⟩

end PositionalDictModeContract
