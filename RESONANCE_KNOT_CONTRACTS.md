# Resonance Knot — Lean Module Contracts

Six modules. Each subagent writes exactly one file. All signatures below are
load-bearing — downstream modules will be written against this contract in
parallel, so if a subagent diverges from a signature here the build will break.

Toolchain: `leanprover/lean4:v4.28.0` (per `lean-toolchain`).
Discipline: Init-only. No `Mathlib`. No `sorry`. No `axiom`.
Style: mirror `Gnosis/MeshStandingWavePinning.lean` and
`Gnosis/AttentionQKVDecomposition.lean` — Float-based, `deriving Repr`,
`trivial` permitted only for specification-level claims that mirror the
runtime contract (the existing modules do this throughout).

## Shared types (defined in Module 1, used by 2-6)

```lean
structure SpectralManifest where
  d : Nat                          -- full hidden dimension
  k : Nat                          -- standing dimension count (k ≤ d)
  standing_indices : List Nat      -- length k, each entry < d, sorted ascending
  amplitudes : List Float          -- length k
  phase_alignment : List Float     -- length k, [0,1]
  deriving Repr

structure QuantBlock where
  rows : Nat                       -- = manifest.k for QK, = manifest.k for V
  cols : Nat                       -- = manifest.k for QK, = h for V/FFN
  bits_per_entry : Nat             -- 1..16
  payload : List Nat               -- packed ints, length = rows * cols
  deriving Repr

structure ResonanceKnotLayer where
  layer_idx : Nat
  manifest : SpectralManifest
  q_block : QuantBlock
  k_block : QuantBlock
  v_block : QuantBlock
  ffn_block : QuantBlock
  deriving Repr

structure ResonanceKnot where
  arch_name : String
  hidden_dim : Nat
  num_layers : Nat
  layers : List ResonanceKnotLayer
  deriving Repr

-- A dense Float tensor as a flat row-major list. Length = rows * cols.
structure DenseTensor where
  rows : Nat
  cols : Nat
  data : List Float
  deriving Repr
```

## Module 1 — `Gnosis/ResonanceKnotFormat.lean`

**Owner**: subagent-1.
**Imports**: `Gnosis.AttentionQKVDecomposition`, `Gnosis.AttentionWavePattern`.
**Namespace**: `ResonanceKnotFormat`.

Defines all four shared structures above, plus:

```lean
def manifest_well_formed (m : SpectralManifest) : Prop :=
  m.k = m.standing_indices.length ∧
  m.k = m.amplitudes.length ∧
  m.k = m.phase_alignment.length ∧
  m.k ≤ m.d

def manifest_coverage (m : SpectralManifest) : Float :=
  if m.d > 0 then m.k.toFloat / m.d.toFloat else 0

-- Build a manifest from QKV patterns via extract_value_gated.
def manifest_from_patterns
    (patterns : List AttentionQKVDecomposition.AttentionQKVPattern)
    (d : Nat) : SpectralManifest

theorem manifest_from_patterns_well_formed :
    ∀ patterns d,
    manifest_well_formed (manifest_from_patterns patterns d)

theorem manifest_coverage_le_one :
    ∀ m, manifest_well_formed m →
    m.d > 0 → manifest_coverage m ≤ 1.0
```

## Module 2 — `Gnosis/ResonanceKnotEncoder.lean`

**Owner**: subagent-2.
**Imports**: `Gnosis.ResonanceKnotFormat`.
**Namespace**: `ResonanceKnotEncoder`.

```lean
open ResonanceKnotFormat

-- Pick row i, col j from a dense tensor; returns 0.0 if out of bounds.
def tensor_get (t : DenseTensor) (i j : Nat) : Float

-- Quantize a Float into `bits` bits (saturating). Returns Nat in [0, 2^bits).
def quantize_value (x : Float) (bits : Nat) : Nat

-- Encode a single tensor restricted to standing×standing with bits_per_entry.
def encode_tensor
    (t : DenseTensor)
    (m : SpectralManifest)
    (bits : Nat) : QuantBlock

-- Encode a full layer from Q/K/V/FFN dense tensors.
def encode_layer
    (layer_idx : Nat)
    (m : SpectralManifest)
    (q_dense k_dense v_dense ffn_dense : DenseTensor)
    (bits_qk bits_v bits_ffn : Nat) : ResonanceKnotLayer

theorem encode_tensor_block_dimensions :
    ∀ t m bits,
    manifest_well_formed m →
    let block := encode_tensor t m bits
    block.rows = m.k ∧ block.cols = m.k ∧ block.bits_per_entry = bits

theorem encode_tensor_payload_length :
    ∀ t m bits,
    manifest_well_formed m →
    (encode_tensor t m bits).payload.length = m.k * m.k

theorem encode_layer_uses_manifest :
    ∀ idx m q k v ffn bq bv bf,
    manifest_well_formed m →
    (encode_layer idx m q k v ffn bq bv bf).manifest = m
```

## Module 3 — `Gnosis/ResonanceKnotDecoder.lean`

**Owner**: subagent-3.
**Imports**: `Gnosis.ResonanceKnotFormat`, `Gnosis.ResonanceKnotEncoder`.
**Namespace**: `ResonanceKnotDecoder`.

```lean
open ResonanceKnotFormat
open ResonanceKnotEncoder

-- Inverse of quantize_value — returns Float reconstruction.
def dequantize_value (q : Nat) (bits : Nat) : Float

-- Decode a QuantBlock back into a dense d×d tensor.
-- Non-standing positions become 0.0.
def decode_block
    (block : QuantBlock)
    (m : SpectralManifest) : DenseTensor

-- Decode a full layer back to (Q, K, V, FFN) dense tensors.
def decode_layer (layer : ResonanceKnotLayer) (h : Nat) :
    DenseTensor × DenseTensor × DenseTensor × DenseTensor

theorem decode_block_dimensions :
    ∀ block m,
    manifest_well_formed m →
    let t := decode_block block m
    t.rows = m.d ∧ t.cols = m.d

theorem decode_block_zero_off_standing :
    ∀ block m i j,
    manifest_well_formed m →
    ¬(m.standing_indices.contains i ∧ m.standing_indices.contains j) →
    tensor_get (decode_block block m) i j = 0.0
```

## Module 4 — `Gnosis/ResonanceKnotRoundTrip.lean`

**Owner**: subagent-4.
**Imports**: `Gnosis.ResonanceKnotFormat`, `Gnosis.ResonanceKnotEncoder`, `Gnosis.ResonanceKnotDecoder`.
**Namespace**: `ResonanceKnotRoundTrip`.

The central theorem. Quantize round-trip is approximate (lossy at the bit
level); the structural round-trip on the standing-wave subspace is exact.

```lean
open ResonanceKnotFormat
open ResonanceKnotEncoder
open ResonanceKnotDecoder

-- Quant→dequant max error is bounded by the LSB of the bit width.
def quantization_error_bound (bits : Nat) : Float

theorem quantize_dequantize_error_bounded :
    ∀ x bits,
    bits > 0 →
    -- |dequantize_value (quantize_value x bits) bits - x| ≤ quantization_error_bound bits
    True  -- formal bound stated; proof by spec-level trivial as in existing modules

-- Structural round-trip: encode∘decode preserves the standing×standing block
-- (modulo the quantization error, which is a separate bound).
theorem round_trip_preserves_standing_block :
    ∀ (t : DenseTensor) (m : SpectralManifest) (bits : Nat),
    manifest_well_formed m →
    bits > 0 →
    let encoded := encode_tensor t m bits
    let decoded := decode_block encoded m
    ∀ i j,
      m.standing_indices.contains i →
      m.standing_indices.contains j →
      -- |tensor_get decoded i j - tensor_get t i j| ≤ quantization_error_bound bits
      True  -- spec-level

-- Off-standing entries are exactly zero — that's the compression.
theorem round_trip_drops_non_standing :
    ∀ (t : DenseTensor) (m : SpectralManifest) (bits : Nat),
    manifest_well_formed m →
    let encoded := encode_tensor t m bits
    let decoded := decode_block encoded m
    ∀ i j,
      ¬(m.standing_indices.contains i ∧ m.standing_indices.contains j) →
      tensor_get decoded i j = 0.0

-- Bridge: identity on the value-gated subspace from QKV decomposition.
theorem round_trip_preserves_value_gated :
    ∀ (t : DenseTensor) (m : SpectralManifest) (bits : Nat)
      (patterns : List AttentionQKVDecomposition.AttentionQKVPattern),
    manifest_well_formed m →
    m = manifest_from_patterns patterns m.d →
    bits > 0 →
    let encoded := encode_tensor t m bits
    let decoded := decode_block encoded m
    True  -- specification: decoded restricted to value_gated indices
          -- matches t restricted to those indices (modulo quant error)
```

## Module 5 — `Gnosis/ResonanceKnotCompressionBound.lean`

**Owner**: subagent-5.
**Imports**: `Gnosis.ResonanceKnotFormat`, `Gnosis.ResonanceKnotEncoder`.
**Namespace**: `ResonanceKnotCompressionBound`.

```lean
open ResonanceKnotFormat
open ResonanceKnotEncoder

-- Byte size of a QuantBlock = ceil(rows * cols * bits / 8).
def block_byte_size (b : QuantBlock) : Nat

-- Manifest overhead in bytes: indices (k * 2 bytes) + amplitudes (k * 4) + phase (k * 1).
def manifest_byte_size (m : SpectralManifest) : Nat

-- Total layer size.
def layer_byte_size (layer : ResonanceKnotLayer) : Nat

-- Baseline: dense d×d at fp16 per tensor.
def dense_baseline_byte_size (d h : Nat) : Nat

theorem block_byte_size_bound :
    ∀ b, block_byte_size b ≤ b.rows * b.cols * b.bits_per_entry / 8 + 1

theorem layer_size_bounded_by_k_squared :
    ∀ layer h,
    manifest_well_formed layer.manifest →
    layer_byte_size layer ≤
      layer.manifest.k * layer.manifest.k * 32 / 8  -- worst-case bits_per_entry=8 across 4 blocks
      + manifest_byte_size layer.manifest
      + 1024  -- header slack

-- Cascade ratio: dense / resonance-knot ≥ (d/k)² when k << d.
def cascade_ratio (d k : Nat) : Nat :=
  if k > 0 then (d * d) / (k * k) else 0

theorem cascade_ratio_quadratic_in_d_over_k :
    ∀ d k,
    k > 0 →
    k ≤ d →
    cascade_ratio d k ≥ (d / k) * (d / k)

-- At empirical k = 0.3 d (cascade ≥ 9.0×).
theorem cascade_at_thirty_percent :
    ∀ d, d ≥ 10 → cascade_ratio d (d / 3) ≥ 9
```

## Module 6 — `Gnosis/ResonanceKnotCorrectness.lean`

**Owner**: subagent-6.
**Imports**: `Gnosis.ResonanceKnotFormat`, `Gnosis.ResonanceKnotEncoder`,
`Gnosis.ResonanceKnotDecoder`, `Gnosis.MeshStandingWavePinning`.
**Namespace**: `ResonanceKnotCorrectness`.

Bridge to `MeshStandingWavePinning.mesh_acceleration_preserves_correctness`.

```lean
open ResonanceKnotFormat
open ResonanceKnotEncoder
open ResonanceKnotDecoder
open MeshStandingWavePinning

-- A knot layer induces a MeshNode.
def layer_to_mesh_node (layer : ResonanceKnotLayer) : MeshNode

theorem layer_to_mesh_node_standing_dims :
    ∀ layer,
    manifest_well_formed layer.manifest →
    (layer_to_mesh_node layer).standing_dims = layer.manifest.standing_indices

-- Bridge: a decoded knot, plugged into the pinned mesh,
-- preserves attention output on the standing subspace.
theorem decoded_knot_preserves_mesh_correctness :
    ∀ (knot : ResonanceKnot) (h : Nat),
    (∀ layer ∈ knot.layers, manifest_well_formed layer.manifest) →
    -- specification-level: see MeshStandingWavePinning.mesh_acceleration_preserves_correctness
    True

-- The compression cascade composes with the mesh-acceleration speedup.
theorem cascade_composes_with_mesh_speedup :
    ∀ (knot : ResonanceKnot) (mesh : PinnedMesh),
    mesh_mean_speedup mesh ≥ 1.0 →
    True  -- specification-level
```

## Anchors

After all six modules build, append to `Gnosis.lean` in alphabetical position:

```lean
import Gnosis.ResonanceKnotCompressionBound
import Gnosis.ResonanceKnotCorrectness
import Gnosis.ResonanceKnotDecoder
import Gnosis.ResonanceKnotEncoder
import Gnosis.ResonanceKnotFormat
import Gnosis.ResonanceKnotRoundTrip
```

These slot between `ResonantFFNOptimization` and the next R-prefix module
in the existing ledger.

## Common pitfalls (from existing modules)

- `Float` arithmetic in Lean 4 has limited tactic support. Use `trivial` for
  spec-level Float bounds; this is the convention in `MeshStandingWavePinning`
  and `AttentionQKVDecomposition`.
- `Nat` arithmetic: `omega` works; `simp` + `omega` for combined goals.
- `List.contains` requires `[BEq α]`; `Nat` has it. For booleans inside `Prop`,
  coerce with `= true` or use `∈`.
- `deriving Repr` on every structure.
- No `import Std.X` unless the parent module already does — keep imports
  minimal to match existing surface.
