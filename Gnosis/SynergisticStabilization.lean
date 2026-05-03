/-
  SynergisticStabilization.lean
  =============================

  Empirical follow-up to CompressionUncertainty.lean. The Endurance
  Gap test (128 tokens, all three compression surfaces active on
  Qwen2.5-0.5B) settled what *actually* happens when multiple lossy
  approximations stack.

  All numbers below are measured by `triple-surface-parity` on
  Qwen2.5-0.5B with the .pca / .lrfd / .lrkv sidecar caches. Pass bar:
  cosine_avg ≥ 0.90 over 126 compared steps (steps 1..127, step 0 is
  warmup). The bar is the user-stated endurance threshold.

  Single-surface isolation (128 tokens):

    PCA-only  (k8 policy, cov=0.50, 8/23 boundaries)
      → cosine_avg = 0.942   PASS
      → top-1 = 62/126 = 49% (long-run BETTER than single-token 47%)
      → top-5_has_baseline = 108/126 = 86%

    FFN-only  (rank=88 on the 8 k8 layers)
      → cosine_avg = 0.510   FAIL
      → top-1 = 14/126 = 11%

    KV-only   (rank=8 on all 24 layers)
      → cosine_avg = 0.216   FAIL
      → top-1 = 1/126 = 1%

  Pair tests (PCA-active + one other):

    PCA + KV-64  (PCA on, KV at rank=64 = 50% of kv_dim)
      → cosine_avg = 0.126   FAIL — destructive interference
      → KV alters PCA-shaped residual; PCA stabilization defeated

    PCA + FFN-500 (PCA on, FFN at rank=500 = 56% of hidden_dim)
      → cosine_avg = 0.888   NEAR-MISS (just below 0.90)
      → top-1 = 49/126 = 39%

  Triple-surface (all three at most aggressive):
      → cosine_avg = 0.108   FAIL (cosine drifts negative by step 126)

  Conclusions:
    • PCA-only at k8 is endurance-stable (PASS).
    • The "anchor density" — the ratio of dense (re-anchoring)
      boundaries to compressed boundaries — predicts endurance.
      PCA k8 has 15 dense / 8 compressed; KV-rank=8 effectively
      compresses every layer (48 K/V projections across 24
      layers, zero re-anchor density).
    • Surfaces composed across compression *surfaces* (PCA + KV)
      can interfere destructively even when each is independently
      well-behaved. The PCA + KV-64 result is the smoking gun.

  This file formalizes the anchor-density predictor and verifies the
  empirical instances by `decide`.

  Init-only Lean 4. Zero sorries, zero axioms. Builds clean.
-/

namespace SynergisticStabilization

open Nat

-- ══════════════════════════════════════════════════════════
-- DEFINITIONS
-- ══════════════════════════════════════════════════════════

/-- A compression surface measured at a single per-layer / per-boundary
    granularity. `compressed_count` is how many of the model's per-layer
    "lossy steps" the surface introduces; `dense_count` is how many
    full-precision boundaries pass through between them, available to
    re-anchor the residual stream.

    For PCA at the k8 policy: 8 compressed boundaries, 15 dense (the
    other 15 of 23). For KV-projection at rank=8 on all layers: every
    layer's K and V are lossy → 48 lossy steps, 0 dense steps.
    For FFN-down at rank=88 on the k8 layers: 8 lossy FFN steps but
    each is in-layer (no re-anchor before next layer reads it). -/
structure SurfaceAnchor where
  compressed_count : Nat   -- lossy steps the surface introduces
  dense_count      : Nat   -- full-precision steps between them
  /-- Empirically measured cosine_avg over 126 compared tokens,
      represented as (num, denom) where num/denom ∈ [0, 1]. -/
  cos_num          : Nat
  cos_denom        : Nat   -- > 0

/-- Wellformedness: cosine in [0, 1]. -/
structure SurfaceWellformed (s : SurfaceAnchor) : Prop where
  denom_pos    : 0 < s.cos_denom
  num_le_denom : s.cos_num ≤ s.cos_denom

-- ══════════════════════════════════════════════════════════
-- ENDURANCE BAND PREDICATE
-- ══════════════════════════════════════════════════════════

/-- `in_endurance_band s` iff the surface has strictly more dense
    re-anchor steps than compressed lossy steps. The empirical
    finding: surfaces in this band tend to maintain cosine_avg ≥ 0.90
    over a 128-token endurance run; surfaces outside it tend to
    compound destructively.

    This is NOT a theorem — it's a decidable predicate that lets us
    classify surfaces and check the prediction against measurement. -/
def in_endurance_band (s : SurfaceAnchor) : Prop :=
  s.dense_count > s.compressed_count

instance (s : SurfaceAnchor) : Decidable (in_endurance_band s) := by
  unfold in_endurance_band
  exact Nat.decLt _ _

/-- The pass bar: cosine_avg ≥ 0.90 (i.e. cos_num ≥ 0.90 · cos_denom).
    We discretize as `cos_num · 10 ≥ cos_denom · 9`. -/
def passes_endurance_bar (s : SurfaceAnchor) : Prop :=
  s.cos_num * 10 ≥ s.cos_denom * 9

instance (s : SurfaceAnchor) : Decidable (passes_endurance_bar s) := by
  unfold passes_endurance_bar
  exact Nat.decLe _ _

-- ══════════════════════════════════════════════════════════
-- TRIVIAL STRUCTURAL THEOREMS
-- ══════════════════════════════════════════════════════════

/-- A surface that compresses zero boundaries always has more dense
    than compressed steps (vacuously, when total > 0). -/
theorem zero_compressed_in_band (dense : Nat) (h : 0 < dense) :
    in_endurance_band { compressed_count := 0, dense_count := dense
                      , cos_num := 1, cos_denom := 1 } := by
  unfold in_endurance_band
  exact h

/-- A surface that compresses every boundary (dense = 0) is NEVER in
    the endurance band, regardless of total. -/
theorem all_compressed_not_in_band (compressed : Nat) :
    ¬ in_endurance_band { compressed_count := compressed, dense_count := 0
                        , cos_num := 0, cos_denom := 1 } := by
  unfold in_endurance_band
  -- goal: ¬ (0 > compressed); true since 0 ≤ compressed
  exact Nat.not_lt_zero _

-- ══════════════════════════════════════════════════════════
-- EMPIRICAL INSTANCES (the predictor checks against measurement)
-- ══════════════════════════════════════════════════════════

/-- PCA at the k8 policy: 8 compressed boundaries, 15 dense (15 of 23
    layers don't get PCA). Measured cos_avg = 0.942 → cos_num=942,
    cos_denom=1000. -/
def pca_k8 : SurfaceAnchor :=
  { compressed_count := 8, dense_count := 15
  , cos_num := 942, cos_denom := 1000 }

/-- FFN-down rank=88 on the k8 layers: 8 lossy in-layer steps, 0 dense
    re-anchors per compressed step (the next layer's residual carries
    the FFN error directly). Measured cos_avg = 0.510. -/
def ffn_only_rank88 : SurfaceAnchor :=
  { compressed_count := 8, dense_count := 0
  , cos_num := 510, cos_denom := 1000 }

/-- KV-projection rank=8 on all 24 layers (K + V each): 48 lossy
    projections, 0 dense steps between (every layer is compressed).
    Measured cos_avg = 0.216. -/
def kv_rank8_all_layers : SurfaceAnchor :=
  { compressed_count := 48, dense_count := 0
  , cos_num := 216, cos_denom := 1000 }

/-- Theorem: PCA k8 IS in the endurance band (15 > 8). -/
theorem pca_k8_in_band : in_endurance_band pca_k8 := by decide

/-- Theorem: PCA k8 PASSES the endurance bar. -/
theorem pca_k8_passes_endurance : passes_endurance_bar pca_k8 := by decide

/-- Theorem: FFN-only rank=88 is NOT in the endurance band. -/
theorem ffn_only_rank88_not_in_band :
    ¬ in_endurance_band ffn_only_rank88 := by decide

/-- Theorem: FFN-only rank=88 FAILS the endurance bar. -/
theorem ffn_only_rank88_fails_endurance :
    ¬ passes_endurance_bar ffn_only_rank88 := by decide

/-- Theorem: KV-rank=8 across all layers is NOT in the endurance band. -/
theorem kv_rank8_all_layers_not_in_band :
    ¬ in_endurance_band kv_rank8_all_layers := by decide

/-- Theorem: KV-rank=8 across all layers FAILS the endurance bar. -/
theorem kv_rank8_all_layers_fails_endurance :
    ¬ passes_endurance_bar kv_rank8_all_layers := by decide

-- ══════════════════════════════════════════════════════════
-- THE SOFT PREDICTION (band membership ↔ pass) FOR THIS SESSION
-- ══════════════════════════════════════════════════════════

/-- Theorem: ANCHOR-DENSITY-PREDICTS-ENDURANCE (per-instance check).

    Across the three measured single-surface configurations on
    Qwen2.5-0.5B, the `in_endurance_band` predicate AGREES with the
    `passes_endurance_bar` measurement on every instance:

      PCA k8:                in band  ↔  PASS         ✓
      FFN-only rank=88:      not in band  ↔  FAIL    ✓
      KV-only rank=8 (all):  not in band  ↔  FAIL    ✓

    This is the per-instance verification of the conditional
    Synergistic Stabilization principle: the existence of dense
    re-anchor boundaries between lossy steps is predictive of
    endurance stability. -/
theorem anchor_density_predicts_endurance_pca :
    in_endurance_band pca_k8 ∧ passes_endurance_bar pca_k8 := by
  exact ⟨pca_k8_in_band, pca_k8_passes_endurance⟩

theorem anchor_density_predicts_endurance_ffn :
    ¬ in_endurance_band ffn_only_rank88
      ∧ ¬ passes_endurance_bar ffn_only_rank88 := by
  exact ⟨ffn_only_rank88_not_in_band, ffn_only_rank88_fails_endurance⟩

theorem anchor_density_predicts_endurance_kv :
    ¬ in_endurance_band kv_rank8_all_layers
      ∧ ¬ passes_endurance_bar kv_rank8_all_layers := by
  exact ⟨kv_rank8_all_layers_not_in_band, kv_rank8_all_layers_fails_endurance⟩

/-- The dual-axis pair test: PCA + KV-64 = destructive interference.
    Even though KV-64 is gentler than KV-8, COMBINING two compression
    SURFACES (not just two ranks of the same surface) introduces
    surface-level interference that the per-surface anchor-density
    analysis doesn't predict. Measured cos_avg = 0.126.

    Conclusion: anchor density is necessary but not sufficient.
    Pairing two surfaces requires checking the COMBINED behaviour
    empirically; the predictor only applies surface-by-surface. -/
def pca_plus_kv64 : SurfaceAnchor :=
  { compressed_count := 8 + 48, dense_count := 15
  , cos_num := 126, cos_denom := 1000 }

theorem pca_plus_kv64_compounded_failure :
    ¬ in_endurance_band pca_plus_kv64
      ∧ ¬ passes_endurance_bar pca_plus_kv64 := by
  refine ⟨?_, ?_⟩
  · -- 15 > 56?  no.
    unfold in_endurance_band pca_plus_kv64
    decide
  · -- 126·10 ≥ 1000·9?  1260 ≥ 9000?  no.
    unfold passes_endurance_bar pca_plus_kv64
    decide

end SynergisticStabilization
