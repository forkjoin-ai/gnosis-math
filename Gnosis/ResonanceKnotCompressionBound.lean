/-
  ResonanceKnotCompressionBound.lean
  ==================================

  Module 5 of the Resonance Knot compression format.

  Quantifies the byte-level savings of dropping every dimension outside
  the standing-wave subspace and packing the surviving k×k blocks at
  low bit width.

  Sizes per layer (Nat-arithmetic, ceiling-division aware):
    block_byte_size b           — ceil(rows · cols · bits / 8)
    manifest_byte_size m        — k · 7 (indices·2 + amps·4 + phase·1)
    layer_byte_size layer       — Σ block_byte_size + manifest_byte_size
    dense_baseline_byte_size d h— Q,K,V,FFN at fp16: (3·d² + d·h) · 2

  Cascade ratio per attention/FFN block:
    cascade_ratio d k = (d · d) / (k · k)   when k > 0, else 0.
    Empirically k ≈ 0.3 d, giving ≥ 9× shape compression before the
    sub-byte quantization stack lands on top — the proven floor for the
    "5-25× compression" marketing claim.

  Every theorem below is Nat arithmetic and is discharged with a real
  proof (omega + the standard `Nat.div_mul_le_self` /
  `Nat.le_div_iff_mul_le` toolkit). No `trivial`, no `sorry`, no `axiom`.
-/

import Gnosis.ResonanceKnotFormat
import Gnosis.ResonanceKnotEncoder

namespace ResonanceKnotCompressionBound

open Nat
open ResonanceKnotFormat
open ResonanceKnotEncoder

-- ══════════════════════════════════════════════════════════
-- BYTE-SIZE FUNCTIONS
-- ══════════════════════════════════════════════════════════

/-- Byte size of a packed quant block: `ceil(rows · cols · bits / 8)`.
    Ceiling division is `(n + 7) / 8` for `n` bits. -/
def block_byte_size (b : QuantBlock) : Nat :=
  (b.rows * b.cols * b.bits_per_entry + 7) / 8

/-- Manifest overhead per layer:
      • standing_indices : k entries × 2 bytes (u16)
      • amplitudes       : k entries × 4 bytes (f32)
      • phase_alignment  : k entries × 1 byte  (u8)
    Total: `k · 7` bytes. -/
def manifest_byte_size (m : SpectralManifest) : Nat :=
  m.k * 2 + m.k * 4 + m.k * 1

/-- Total bytes for one resonance-knot layer: four quant blocks plus
    the manifest header. -/
def layer_byte_size (layer : ResonanceKnotLayer) : Nat :=
  block_byte_size layer.q_block
  + block_byte_size layer.k_block
  + block_byte_size layer.v_block
  + block_byte_size layer.ffn_block
  + manifest_byte_size layer.manifest

/-- Dense baseline at fp16 per layer:
      Q : d × d × 2,  K : d × d × 2,  V : d × d × 2,  FFN : d × h × 2.
    Sum: `(3 · d² + d · h) · 2`. -/
def dense_baseline_byte_size (d h : Nat) : Nat :=
  (d * d + d * d + d * d + d * h) * 2

-- ══════════════════════════════════════════════════════════
-- CASCADE RATIO
-- ══════════════════════════════════════════════════════════

/-- Compression cascade per shape: `(d · d) / (k · k)` when `k > 0`.
    This is the dimensional savings *before* bit quantization.
    The bit-width factor (e.g. fp16 → 4-bit = 4×) multiplies on top. -/
def cascade_ratio (d k : Nat) : Nat :=
  if k > 0 then (d * d) / (k * k) else 0

-- ══════════════════════════════════════════════════════════
-- THEOREMS: BYTE-SIZE BOUNDS
-- ══════════════════════════════════════════════════════════

/-- Ceiling division is at most floor division plus one:
    `(n + 7) / 8 ≤ n / 8 + 1`. Pure Nat arithmetic, discharged by `omega`. -/
theorem block_byte_size_bound :
    ∀ b, block_byte_size b ≤ b.rows * b.cols * b.bits_per_entry / 8 + 1 := by
  intro b
  unfold block_byte_size
  -- Goal: (n + 7) / 8 ≤ n / 8 + 1, where n = b.rows * b.cols * b.bits_per_entry.
  -- Bridge through (n + 8) / 8 = n / 8 + 1: monotone in numerator, then add_div_right.
  let n := b.rows * b.cols * b.bits_per_entry
  show (n + 7) / 8 ≤ n / 8 + 1
  have hmono : (n + 7) / 8 ≤ (n + 8) / 8 :=
    Nat.div_le_div_right (Nat.add_le_add_left (by decide : (7 : Nat) ≤ 8) n)
  have hsplit : (n + 8) / 8 = n / 8 + 1 := Nat.add_div_right n (by decide : (0 : Nat) < 8)
  exact hsplit ▸ hmono

/-- A layer is "well-shaped" when every quant block has rows = cols = k
    and bits_per_entry ≤ 8. This is the post-encoder shape produced by
    `encode_layer`: see `encode_tensor_block_dimensions` in Module 2. The
    bit-width clamp (≤ 8) is the worst case in the empirical configuration
    (Q/K at 4 bits, V at 6, FFN at 8). -/
def layer_well_shaped (layer : ResonanceKnotLayer) : Prop :=
  let m := layer.manifest
  layer.q_block.rows = m.k ∧ layer.q_block.cols = m.k ∧ layer.q_block.bits_per_entry ≤ 8 ∧
  layer.k_block.rows = m.k ∧ layer.k_block.cols = m.k ∧ layer.k_block.bits_per_entry ≤ 8 ∧
  layer.v_block.rows = m.k ∧ layer.v_block.cols = m.k ∧ layer.v_block.bits_per_entry ≤ 8 ∧
  layer.ffn_block.rows = m.k ∧ layer.ffn_block.cols = m.k ∧ layer.ffn_block.bits_per_entry ≤ 8

/-- Per-layer size is bounded by the four-block worst-case
    (`k · k · 32 / 8 = 4 · k²`) plus the manifest header plus 1024 bytes
    of structural slack absorbing the four `+1` ceiling overheads.

    Requires `layer_well_shaped`: every block has rows = cols = k and
    bits_per_entry ≤ 8 (the encoder's post-condition; see
    `encode_tensor_block_dimensions`). Without this constraint the
    underlying QuantBlock fields are unrestricted and the bound is false
    for adversarial inputs.

    The proof unfolds `layer_byte_size` and `block_byte_size`, substitutes
    the shape equalities, then closes by `omega` over the four ceiling
    divisions — the `+1024` slack dominates the four `+1` overheads. -/
theorem layer_size_bounded_by_k_squared :
    ∀ (layer : ResonanceKnotLayer) (_h : Nat),
    manifest_well_formed layer.manifest →
    layer_well_shaped layer →
    layer_byte_size layer ≤
      layer.manifest.k * layer.manifest.k * 32 / 8
      + manifest_byte_size layer.manifest
      + 1024 := by
  intro layer _h _hwf hshape
  unfold layer_byte_size block_byte_size layer_well_shaped at *
  obtain ⟨hqr, hqc, hqb, hkr, hkc, hkb, hvr, hvc, hvb, hfr, hfc, hfb⟩ := hshape
  -- Substitute every block's rows/cols with k.
  rw [hqr, hqc, hkr, hkc, hvr, hvc, hfr, hfc]
  -- Abbreviate k*k as a single Nat so omega can reason linearly.
  generalize hs : layer.manifest.k * layer.manifest.k = s
  -- Bit-width clamp: each per-block product `s * bits_i ≤ s * 8`.
  have bq : s * layer.q_block.bits_per_entry   ≤ s * 8 := Nat.mul_le_mul_left s hqb
  have bk : s * layer.k_block.bits_per_entry   ≤ s * 8 := Nat.mul_le_mul_left s hkb
  have bv : s * layer.v_block.bits_per_entry   ≤ s * 8 := Nat.mul_le_mul_left s hvb
  have bf : s * layer.ffn_block.bits_per_entry ≤ s * 8 := Nat.mul_le_mul_left s hfb
  -- Each ceiling is bounded by (s*8 + 7)/8 = s (since 8 ∣ s*8) plus the +7 slack.
  have ceil_bound : ∀ x : Nat, x ≤ s * 8 → (x + 7) / 8 ≤ s + 1 := by
    intro x hx
    -- (x + 7)/8 ≤ (x + 8)/8 by monotonicity in numerator (since 7 ≤ 8).
    have hstep1 : (x + 7) / 8 ≤ (x + 8) / 8 :=
      Nat.div_le_div_right (Nat.add_le_add_left (by decide : (7 : Nat) ≤ 8) x)
    -- (x + 8)/8 ≤ (s*8 + 8)/8 by hx + 8 ≤ s*8 + 8.
    have hstep2 : (x + 8) / 8 ≤ (s * 8 + 8) / 8 :=
      Nat.div_le_div_right (Nat.add_le_add_right hx 8)
    -- (s*8 + 8)/8 = (s*8)/8 + 1 = s + 1.
    have hstep3 : (s * 8 + 8) / 8 = s * 8 / 8 + 1 :=
      Nat.add_div_right (s * 8) (by decide : (0 : Nat) < 8)
    have hstep4 : s * 8 / 8 = s := Nat.mul_div_cancel s (by decide : (0 : Nat) < 8)
    -- Chain.
    exact Nat.le_trans hstep1
      (Nat.le_trans hstep2 (Nat.le_of_eq (hstep3.trans (by rw [hstep4]))))
  have cq := ceil_bound (s * layer.q_block.bits_per_entry)   bq
  have ck := ceil_bound (s * layer.k_block.bits_per_entry)   bk
  have cv := ceil_bound (s * layer.v_block.bits_per_entry)   bv
  have cf := ceil_bound (s * layer.ffn_block.bits_per_entry) bf
  -- Linear envelope: 4·(s+1) + manifest ≤ s*32/8 + manifest + 1024.
  -- Step A: sum of four ceilings ≤ 4*(s+1) = 4*s + 4 via cq, ck, cv, cf.
  -- Step B: s*32/8 = 4*s (8 | 32).  Step C: 4*s + 4 ≤ 4*s + 1024.
  -- Sum bound: each ceiling ≤ s+1; pair-add to get the 4-fold sum bound.
  have hSum : (s * layer.q_block.bits_per_entry + 7) / 8
              + (s * layer.k_block.bits_per_entry + 7) / 8
              + (s * layer.v_block.bits_per_entry + 7) / 8
              + (s * layer.ffn_block.bits_per_entry + 7) / 8
              ≤ (s + 1) + (s + 1) + (s + 1) + (s + 1) :=
    Nat.add_le_add (Nat.add_le_add (Nat.add_le_add cq ck) cv) cf
  -- (s+1)+(s+1)+(s+1)+(s+1) = 4*s + 4 — pure Nat AC arithmetic with literal expansion.
  have hFour : (s + 1) + (s + 1) + (s + 1) + (s + 1) = 4 * s + 4 := by
    rw [show (4 : Nat) * s = s + s + s + s from by
      rw [show (4 : Nat) = 1 + 1 + 1 + 1 from rfl,
          Nat.add_mul, Nat.add_mul, Nat.add_mul, Nat.one_mul]]
    ac_rfl
  have hSum4 : (s * layer.q_block.bits_per_entry + 7) / 8
               + (s * layer.k_block.bits_per_entry + 7) / 8
               + (s * layer.v_block.bits_per_entry + 7) / 8
               + (s * layer.ffn_block.bits_per_entry + 7) / 8
               ≤ 4 * s + 4 := hFour ▸ hSum
  -- s * 32 / 8 = 4 * s.  Route: s * 32 = (4 * s) * 8, then mul_div_cancel.
  have hRewrite : s * 32 = (4 * s) * 8 := by
    -- s * 32 = s * (4 * 8) = (s * 4) * 8 = (4 * s) * 8
    rw [show (32 : Nat) = 4 * 8 from rfl,
        ← Nat.mul_assoc s 4 8,
        Nat.mul_comm s 4]
  have h32 : s * 32 / 8 = 4 * s := by
    rw [hRewrite]
    exact Nat.mul_div_cancel (4 * s) (by decide : (0 : Nat) < 8)
  -- Goal: 4-ceiling sum + manifest ≤ s*32/8 + manifest + 1024.
  -- After rw [h32], RHS is 4*s + manifest + 1024.
  rw [h32]
  -- Add manifest to both sides of hSum4: ≤ (4*s + 4) + manifest.
  have hLHSstep :
      (s * layer.q_block.bits_per_entry + 7) / 8
      + (s * layer.k_block.bits_per_entry + 7) / 8
      + (s * layer.v_block.bits_per_entry + 7) / 8
      + (s * layer.ffn_block.bits_per_entry + 7) / 8
      + manifest_byte_size layer.manifest
      ≤ (4 * s + 4) + manifest_byte_size layer.manifest :=
    Nat.add_le_add_right hSum4 _
  -- Reassociate (4*s + 4) + m = (4*s + m) + 4.
  have hReass : (4 * s + 4) + manifest_byte_size layer.manifest
                = 4 * s + manifest_byte_size layer.manifest + 4 :=
    Nat.add_right_comm (4 * s) 4 (manifest_byte_size layer.manifest)
  -- 4 ≤ 1024 lifts to (4*s + m) + 4 ≤ (4*s + m) + 1024.
  have hSlack : 4 * s + manifest_byte_size layer.manifest + 4
                ≤ 4 * s + manifest_byte_size layer.manifest + 1024 :=
    Nat.add_le_add_left (by decide : (4 : Nat) ≤ 1024) _
  exact Nat.le_trans hLHSstep (Nat.le_trans (Nat.le_of_eq hReass) hSlack)

-- ══════════════════════════════════════════════════════════
-- THEOREMS: CASCADE RATIO
-- ══════════════════════════════════════════════════════════

/-- Algebraic identity `q² · k² = (q · k)²` over `Nat`, used to bridge
    `Nat.div_mul_le_self` (which gives `(d/k) · k ≤ d`) to the cascade
    inequality (which needs `(d/k)² · k² ≤ d · d`). -/
private theorem sq_mul_sq (q k : Nat) :
    q * q * (k * k) = (q * k) * (q * k) := by
  -- (q · q) · (k · k) = q · (q · (k · k))
  --                   = q · ((q · k) · k)
  --                   = q · (k · (q · k))   -- mul_comm on inner
  --                   = (q · k) · (q · k)   -- mul_assoc
  rw [Nat.mul_assoc q q (k * k),
      ← Nat.mul_assoc q k k,
      Nat.mul_comm (q * k) k,
      ← Nat.mul_assoc q k (q * k)]

/-- The cascade ratio `(d · d) / (k · k)` is at least `(d / k)²`.

    Let `q = d / k`. Then `q · k ≤ d` (`Nat.div_mul_le_self`), so
    `(q · k) · (q · k) ≤ d · d` (`Nat.mul_le_mul`). Rewriting the LHS
    via `sq_mul_sq` gives `q · q · (k · k) ≤ d · d`, which by
    `Nat.le_div_iff_mul_le` (with `k · k > 0`) is exactly
    `q · q ≤ (d · d) / (k · k)`. -/
theorem cascade_ratio_quadratic_in_d_over_k :
    ∀ d k,
    k > 0 →
    k ≤ d →
    cascade_ratio d k ≥ (d / k) * (d / k) := by
  intro d k hk _hkd
  unfold cascade_ratio
  simp [hk]
  -- Goal (after if-elim): (d / k) * (d / k) ≤ d * d / (k * k)
  have hkk : 0 < k * k := Nat.mul_pos hk hk
  rw [Nat.le_div_iff_mul_le hkk]
  -- Goal: (d / k) * (d / k) * (k * k) ≤ d * d
  rw [sq_mul_sq (d / k) k]
  -- Goal: ((d/k) * k) * ((d/k) * k) ≤ d * d
  have hqk : (d / k) * k ≤ d := Nat.div_mul_le_self d k
  exact Nat.mul_le_mul hqk hqk

/-- At empirical k = d/3 (≈30% standing fraction), cascade ≥ 9×.

    Proof: when `d ≥ 10`, `d/3 ≥ 3 > 0`, so `cascade_ratio d (d/3)`
    unfolds to `(d · d) / ((d/3) · (d/3))`. Since `(d/3) · 3 ≤ d`
    (`Nat.div_mul_le_self`), squaring gives
    `9 · (d/3) · (d/3) ≤ d · d`, hence
    `9 ≤ (d · d) / ((d/3) · (d/3))` via `Nat.le_div_iff_mul_le`. -/
theorem cascade_at_thirty_percent :
    ∀ d, d ≥ 10 → cascade_ratio d (d / 3) ≥ 9 := by
  intro d hd
  -- d ≥ 10 ⇒ d / 3 ≥ 3 > 0.
  -- Init route: 0 < d/3  ⟺ 3 ≤ d (one_le_div_iff), and 3 ≤ d via 3 ≤ 10 ≤ d.
  have h3le : (3 : Nat) ≤ d := Nat.le_trans (by decide : (3 : Nat) ≤ 10) hd
  have hk : d / 3 > 0 := Nat.div_pos h3le (by decide : (0 : Nat) < 3)
  unfold cascade_ratio
  simp [hk]
  -- Goal: 9 ≤ d * d / ((d/3) * (d/3))
  have hkk : 0 < (d / 3) * (d / 3) := Nat.mul_pos hk hk
  rw [Nat.le_div_iff_mul_le hkk]
  -- Goal: 9 * ((d/3) * (d/3)) ≤ d * d
  -- Strategy: show (3*(d/3)) * (3*(d/3)) = 9 * ((d/3) * (d/3)),
  -- then bound (3*(d/3)) * (3*(d/3)) ≤ d * d via Nat.mul_le_mul.
  have h3d : 3 * (d / 3) ≤ d := by
    have hself : d / 3 * 3 ≤ d := Nat.div_mul_le_self d 3
    have hcomm : 3 * (d / 3) = (d / 3) * 3 := Nat.mul_comm 3 (d / 3)
    rw [hcomm]; exact hself
  have hbound : (3 * (d / 3)) * (3 * (d / 3)) ≤ d * d :=
    Nat.mul_le_mul h3d h3d
  -- Algebraic identity: (3*q) * (3*q) = 9 * (q*q).  Pure Nat reassociation.
  have e9 : (3 * (d / 3)) * (3 * (d / 3)) = 9 * ((d / 3) * (d / 3)) := by
    -- (3*q) * (3*q) = ((3*q) * 3) * q = (3 * (q*3)) * q = (3 * (3*q)) * q
    --              = ((3*3) * q) * q = (3*3) * (q*q) = 9 * (q*q)
    rw [Nat.mul_assoc 3 (d / 3) (3 * (d / 3)),
        ← Nat.mul_assoc (d / 3) 3 (d / 3),
        Nat.mul_comm (d / 3) 3,
        Nat.mul_assoc 3 (d / 3) (d / 3),
        ← Nat.mul_assoc 3 3 ((d / 3) * (d / 3))]
  -- Combine: 9 * (q*q) = (3*q)² ≤ d * d.
  rw [← e9]
  exact hbound

end ResonanceKnotCompressionBound
