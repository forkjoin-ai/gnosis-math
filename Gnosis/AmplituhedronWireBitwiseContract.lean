/-
  AmplituhedronWireBitwiseContract.lean
  =====================================

  Pins the binary wire format for amplituhedron replay/capture.
  Mirrors the canonical *_runtime_oracle_* pentad pattern.

  Imports Init plus AmplituhedronFalsifiability. Zero sorry,
  zero new axiom.

  2026-05-10 swap: the gzip-interim layer was retired and bit 2 of
  the flags byte was reclaimed as reserved-zero. The payload is now
  the canonical `.bw` framed blob (see `bitwise::bw_codec::encode_bw`
  / `decode_bw`). The pentad below pins only the BWAH-envelope fields
  the wire still owns; the `.bw` payload format has its own contract.
-/

import Init
import Gnosis.AmplituhedronFalsifiability

namespace AmplituhedronWireBitwiseContract

open AmplituhedronFalsifiability

/-! ## The wire format invariants

We formalize the wire as a Nat byte sequence with header fields and
a payload. The runtime (TS + Rust) reproduces the byte values pinned
here on the same canonical witnesses. -/

/-- Magic bytes: `BWAH` = [0x42, 0x57, 0x41, 0x48]. -/
def magicBytes : List Nat := [0x42, 0x57, 0x41, 0x48]

/-- Current wire version. -/
def wireVersion : Nat := 0x01

/-- Flag bit 0 = hit, bit 1 = tail_residual present.
    Bits 2..7 are reserved-zero (the 2026-05-10 gzip swap reclaimed
    bit 2 when the payload codec moved to `bitwise::bw_codec`). -/
def hitFlag : Nat := 0x01
def tailPresentFlag : Nat := 0x02

/-- Header length in bytes for a REPLY:
    4 (magic) + 1 (version) + 1 (flags) + 4 (tail_len) + 4 (kv_slab_len) = 14. -/
def replyHeaderLen : Nat := 14

/-- Header length in bytes for a CAPTURE (adds: u64 prefix_hash, u32 prefix_len, u16 layer_lo, u16 layer_hi):
    14 + 8 + 4 + 2 + 2 = 30. -/
def captureHeaderLen : Nat := 30

/-! ## Runtime oracle pentad -/

/-- Contract #1. Magic bytes have a fixed identity. -/
theorem magic_bytes_oracle :
    magicBytes = [66, 87, 65, 72] := by
  unfold magicBytes; decide

/-- Contract #2. Wire version is exactly 1. -/
theorem wire_version_oracle :
    wireVersion = 1 := by
  unfold wireVersion; decide

/-- Contract #3. Reply header is 14 bytes. -/
theorem reply_header_len_oracle :
    replyHeaderLen = 14 := by
  unfold replyHeaderLen; decide

/-- Contract #4. Capture header is 30 bytes (14 + 16 extra). -/
theorem capture_header_len_oracle :
    captureHeaderLen = 30 := by
  unfold captureHeaderLen; decide

/-- Contract #5. Flag bit identities. -/
theorem flag_bits_oracle :
    hitFlag = 1 ∧ tailPresentFlag = 2 := by
  unfold hitFlag tailPresentFlag; refine ⟨?_, ?_⟩ <;> decide

/-! ## Bundled pentad -/

theorem amplituhedron_wire_bitwise_pentad :
    magicBytes = [66, 87, 65, 72] ∧
    wireVersion = 1 ∧
    replyHeaderLen = 14 ∧
    captureHeaderLen = 30 ∧
    (hitFlag = 1 ∧ tailPresentFlag = 2) :=
  ⟨magic_bytes_oracle, wire_version_oracle,
   reply_header_len_oracle, capture_header_len_oracle,
   flag_bits_oracle⟩

end AmplituhedronWireBitwiseContract
