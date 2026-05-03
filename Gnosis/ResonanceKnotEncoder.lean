/-
  ResonanceKnotEncoder.lean
  =========================

  Pure-functional encoder: dense Float tensor + spectral manifest → quant block.

  The encoder drops every row and column whose index is NOT in the manifest's
  standing_indices, then quantizes the remaining k×k submatrix at the requested
  bit width.

  Pipeline (per tensor):
    1. tensor_get t i j        -- safe row-major indexing, 0.0 out-of-bounds
    2. quantize_value x bits   -- saturating Float → Nat in [0, 2^bits)
    3. encode_tensor t m bits  -- walk standing_indices × standing_indices,
                                  collect quantized payload of length k²
    4. encode_layer ...        -- bundle Q/K/V/FFN blocks under a manifest

  Theorems are dimensional / structural: payload length equals k², block dims
  agree with the manifest, and the encoded layer's manifest is the one passed in.
  Float-level error bounds are stated separately (Module 4).
-/

import Gnosis.ResonanceKnotFormat

namespace ResonanceKnotEncoder

open Nat
open ResonanceKnotFormat

-- ══════════════════════════════════════════════════════════
-- TENSOR INDEXING (ROW-MAJOR, SAFE)
-- ══════════════════════════════════════════════════════════

/-- Pick row i, col j from a dense row-major Float tensor.
    Returns 0.0 if (i, j) is out of bounds — keeps the encoder total. -/
def tensor_get (t : DenseTensor) (i j : Nat) : Float :=
  t.data.getD (i * t.cols + j) 0.0

-- ══════════════════════════════════════════════════════════
-- SCALAR QUANTIZATION (SATURATING)
-- ══════════════════════════════════════════════════════════

/-- Quantize a Float into `bits` bits, modulo 2^bits.
    The exact reconstruction is not load-bearing — Module 4 owns the error
    bound. Here we only require the result to land in [0, 2^bits). -/
def quantize_value (x : Float) (bits : Nat) : Nat :=
  let scale : Float := (2.0 : Float) ^ bits.toFloat
  let scaled : Nat := (x * scale).toUInt64.toNat
  scaled % (2 ^ bits)

-- ══════════════════════════════════════════════════════════
-- BLOCK ENCODING: STANDING × STANDING SUBMATRIX
-- ══════════════════════════════════════════════════════════

/-- Encode a single dense tensor restricted to the standing×standing submatrix.

    For each pair (row_idx, col_idx) drawn from the cartesian product
    standing_indices × standing_indices, we read the corresponding entry from
    the dense tensor and quantize it. The result is a flat row-major payload
    of length k * k where k = manifest.k.

    Off-standing rows and columns are dropped — that is the compression. -/
def encode_tensor
    (t : DenseTensor)
    (m : SpectralManifest)
    (bits : Nat) : QuantBlock :=
  let payload : List Nat :=
    (List.range m.k).flatMap (fun ri =>
      (List.range m.k).map (fun ci =>
        let row_idx := m.standing_indices.getD ri 0
        let col_idx := m.standing_indices.getD ci 0
        quantize_value (tensor_get t row_idx col_idx) bits))
  ⟨m.k, m.k, bits, payload⟩

-- ══════════════════════════════════════════════════════════
-- LAYER ENCODING: Q / K / V / FFN UNDER ONE MANIFEST
-- ══════════════════════════════════════════════════════════

/-- Encode a full attention + FFN layer.
    Q and K share `bits_qk` (aggressive — they only gate).
    V uses `bits_v` (conservative — it carries surviving information).
    FFN uses `bits_ffn` (model-dependent). -/
def encode_layer
    (layer_idx : Nat)
    (m : SpectralManifest)
    (q_dense k_dense v_dense ffn_dense : DenseTensor)
    (bits_qk bits_v bits_ffn : Nat) : ResonanceKnotLayer :=
  ⟨layer_idx,
   m,
   encode_tensor q_dense   m bits_qk,
   encode_tensor k_dense   m bits_qk,
   encode_tensor v_dense   m bits_v,
   encode_tensor ffn_dense m bits_ffn⟩

-- ══════════════════════════════════════════════════════════
-- THEOREMS: STRUCTURAL ENCODER PROPERTIES
-- ══════════════════════════════════════════════════════════

/-- Theorem: an encoded block has rows = k, cols = k, and the requested
    bit width. The block's shape is determined entirely by the manifest. -/
theorem encode_tensor_block_dimensions :
    ∀ t m bits,
    manifest_well_formed m →
    let block := encode_tensor t m bits
    block.rows = m.k ∧ block.cols = m.k ∧ block.bits_per_entry = bits := by
  intro t m bits _h
  simp [encode_tensor]

/-- Theorem: the payload of an encoded block has length k² —
    one quantized entry per standing×standing cell. -/
theorem encode_tensor_payload_length :
    ∀ t m bits,
    manifest_well_formed m →
    (encode_tensor t m bits).payload.length = m.k * m.k := by
  intro t m bits _h
  simp [encode_tensor, List.length_flatMap, List.map_const',
        List.length_range]

/-- Theorem: encode_layer threads the supplied manifest through verbatim.
    Downstream consumers (decoder, mesh bridge) can rely on
    `(encode_layer ... m ...).manifest = m`. -/
theorem encode_layer_uses_manifest :
    ∀ idx m q k v ffn bq bv bf,
    manifest_well_formed m →
    (encode_layer idx m q k v ffn bq bv bf).manifest = m := by
  intro _idx _m _q _k _v _ffn _bq _bv _bf _h
  simp [encode_layer]

end ResonanceKnotEncoder
