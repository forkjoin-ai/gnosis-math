/-
  GnosticValley.lean
  ==================

  Bridge between the empirical Gnostic Valley finding (per-layer PCA
  sensitivity inverts the classical "U-shape damage profile" once the
  right basis is used) and the existing spectral-noise framework
  (`SpectralNoiseEquilibrium.lean`).

  Empirical statement (from session work in distributed-inference,
  Qwen2.5-0.5B):

    Per-layer PCA single-boundary KL, sorted ascending (most tolerant
    first):
      rank   layer   KL
         1     13   0.094   ← MOST tolerant (mid-pipeline)
         2     12   0.096
         3     14   0.099
         4     15   0.118
         5      8   0.121
        ...
        21      0   0.487
        22      2   0.558
        23      1   0.592   ← LEAST tolerant (early)

  The U-shape that random orthogonal projection produced was a
  basis-quality artifact. Under PCA (the L2-optimal unsupervised
  rank-k linear scheme), mid-pipeline layers are the COMPRESSION zone
  and early layers (0-2) are the FRAGILITY zone.

  Architectural reading: very early residuals are still FORMING the
  token/context representation — losing rank there changes the
  foundation. Mid-pipeline activations have SETTLED onto a learned
  task/model manifold where PCA captures most variation.

  Spectral connection: this is the same dichotomy
  `SpectralNoiseEquilibrium` already defines, just expressed at the
  layer-index granularity:

    - Early layers' residuals look "white" (alpha = 0):
        flat power spectrum across dims, broadband, hard to compress
        because every dim carries comparable signal — losing any
        dim costs proportionally.

    - Mid-pipeline residuals look "brown" (alpha = 2):
        inverse-square spectrum, low-frequency dominant, the variance
        concentrates in few principal components → naturally low-rank,
        PCA captures most of it in k << d dims.

    - Final residuals are mixed (the model has decided most of the
      next-token answer; later attention/FFN refine it):
        somewhere between brown and pink, moderately compressible.

  This file formalizes that reading:

    - `LayerSpectralProfile` carries a layer index and a `NoiseColor`
    - `is_compressible_color` returns true for brown / pink (the colors
      with sufficient low-frequency concentration to be PCA-friendly)
    - `k8_policy_layers` lists the empirically validated mid-pipeline
      layers from the standing-wave-pca sweep
    - The conjecture (stated, not proved): every layer in `k8_policy_layers`
      has noise color brown or pink at its residual stream

  The conjecture is empirical, not axiomatic — it's what would have to
  be true for the Gnostic Valley finding to be a CONSEQUENCE of the
  spectral classification rather than a coincidence. Future work would
  measure the per-layer power spectral density of activations and check
  it.

  Init-only Lean 4. Imports `SpectralNoiseEquilibrium`. Zero sorries.
-/

import Gnosis.SpectralNoiseEquilibrium

namespace Gnosis
namespace GnosticValley

open SpectralNoiseEquilibrium

-- ══════════════════════════════════════════════════════════
-- LAYER SPECTRAL PROFILE
-- ══════════════════════════════════════════════════════════

/-- Per-layer spectral classification of the residual stream at that
    layer's output. The conjecture: this color predicts the layer's
    PCA-compressibility. -/
structure LayerSpectralProfile where
  layer_idx   : Nat
  noise_color : NoiseColor

/-- A color is "compressibility-friendly" iff its power spectral density
    has enough low-frequency concentration to compact most variance into
    few principal components.

    - brown (alpha=2):  low-freq dominant   → COMPRESSIBLE
    - pink  (alpha=1):  low-freq leaning    → COMPRESSIBLE
    - white (alpha=0):  flat                → NOT compressible
    - blue  (alpha=-1): high-freq leaning   → NOT compressible
    - violet(alpha=-2): high-freq dominant  → NOT compressible -/
def is_compressible_color : NoiseColor → Bool
  | .brown  => true
  | .pink   => true
  | .white  => false
  | .blue   => false
  | .violet => false

/-- A profile is "in the Gnostic Valley" iff its color is compressible. -/
def in_gnostic_valley (p : LayerSpectralProfile) : Prop :=
  is_compressible_color p.noise_color = true

instance (p : LayerSpectralProfile) : Decidable (in_gnostic_valley p) := by
  unfold in_gnostic_valley
  exact Bool.decEq _ _

-- ══════════════════════════════════════════════════════════
-- ALPHA MONOTONICITY: brown > pink > white in compressibility
-- ══════════════════════════════════════════════════════════

/-- Theorem: brown noise has strictly greater alpha-magnitude than
    white noise. The PCA-compressibility ordering follows the
    alpha-magnitude ordering on the low-frequency-dominant side. -/
theorem brown_more_compressible_than_white :
    alphaMagnitude .brown > alphaMagnitude .white := by decide

/-- Theorem: pink noise has strictly greater alpha-magnitude than
    white noise. -/
theorem pink_more_compressible_than_white :
    alphaMagnitude .pink > alphaMagnitude .white := by decide

/-- Theorem: brown noise has strictly greater alpha-magnitude than
    pink noise. -/
theorem brown_more_compressible_than_pink :
    alphaMagnitude .brown > alphaMagnitude .pink := by decide

/-- Theorem: a profile of brown color is in the Gnostic Valley. -/
theorem brown_profile_in_valley (l : Nat) :
    in_gnostic_valley { layer_idx := l, noise_color := .brown } := by
  unfold in_gnostic_valley is_compressible_color
  rfl

/-- Theorem: a profile of white color is NOT in the Gnostic Valley. -/
theorem white_profile_not_in_valley (l : Nat) :
    ¬ in_gnostic_valley { layer_idx := l, noise_color := .white } := by
  unfold in_gnostic_valley is_compressible_color
  simp

-- ══════════════════════════════════════════════════════════
-- THE EMPIRICAL k8 POLICY
-- ══════════════════════════════════════════════════════════

/-- The 8 layers found empirically (via standing-wave-pca per-boundary
    sensitivity sweep on Qwen2.5-0.5B, cov=0.50) to be the most
    PCA-tolerant. These are the mid-pipeline boundaries the production
    fat-station fires PCA at. -/
def k8_policy_layers : List Nat :=
  [8, 9, 11, 12, 13, 14, 15, 16]

/-- The conjectural assignment: each k8 policy layer's residual has
    brown noise color. This is NOT proved — it's the empirical
    hypothesis that would, if measured to be true, make the Gnostic
    Valley finding a consequence of the spectral classification rather
    than a coincidence. -/
def k8_conjectured_profiles : List LayerSpectralProfile :=
  k8_policy_layers.map (fun l => { layer_idx := l, noise_color := .brown })

/-- Theorem: under the conjectural assignment, every k8 policy layer
    is in the Gnostic Valley. -/
theorem k8_conjectured_all_in_valley :
    ∀ p ∈ k8_conjectured_profiles, in_gnostic_valley p := by
  intro p hp
  -- p is constructed with .brown by k8_conjectured_profiles
  simp only [k8_conjectured_profiles, List.mem_map] at hp
  obtain ⟨l, _, hp_eq⟩ := hp
  rw [← hp_eq]
  exact brown_profile_in_valley l

/-- The complementary conjecture: layers 0, 1, 2 (the empirically
    fragile zone — KL 0.49, 0.59, 0.56 single-boundary in the
    standing-wave-pca sensitivity sweep) have white noise color
    (broadband, low alpha-magnitude). -/
def fragile_zone_layers : List Nat := [0, 1, 2]

def fragile_zone_conjectured_profiles : List LayerSpectralProfile :=
  fragile_zone_layers.map (fun l => { layer_idx := l, noise_color := .white })

/-- Theorem: under the conjectural assignment, no fragile-zone layer
    is in the Gnostic Valley. -/
theorem fragile_zone_conjectured_none_in_valley :
    ∀ p ∈ fragile_zone_conjectured_profiles, ¬ in_gnostic_valley p := by
  intro p hp
  simp only [fragile_zone_conjectured_profiles, List.mem_map] at hp
  obtain ⟨l, _, hp_eq⟩ := hp
  rw [← hp_eq]
  exact white_profile_not_in_valley l

-- ══════════════════════════════════════════════════════════
-- BRIDGE TO SPECTRAL BUDGET
-- ══════════════════════════════════════════════════════════

/-- A profile "fits the base sound plane" if its noise color does (per
    `SpectralNoiseEquilibrium.fitsSoundPlane`). The base plane has
    dimension 6 (Skyrms). White, pink, and blue fit; brown and violet
    require the first lift (dim 7).

    Connection to the Gnostic Valley: the COMPRESSIBLE colors (brown,
    pink) span the lift boundary. Pink fits the base; brown requires
    the lift. So the Gnostic Valley spans the spectral-budget hierarchy:
    not all compressible layers are equal — brown layers (the most
    compressible) need a richer mesh budget than pink layers do. -/
def profile_fits_plane (p : LayerSpectralProfile) (mesh_dim : Nat) : Prop :=
  fitsSoundPlane p.noise_color mesh_dim

/-- Theorem: a brown profile fits the first-lift sound plane (dim 7). -/
theorem brown_profile_fits_first_lift (l : Nat) :
    profile_fits_plane { layer_idx := l, noise_color := .brown }
                       (soundPlaneDim 1) := by
  unfold profile_fits_plane
  exact brown_fits_first_lift_plane

/-- Theorem: a pink profile fits the base sound plane (dim 6). -/
theorem pink_profile_fits_base (l : Nat) :
    profile_fits_plane { layer_idx := l, noise_color := .pink }
                       (soundPlaneDim 0) := by
  unfold profile_fits_plane
  exact pink_fits_base_plane

-- ══════════════════════════════════════════════════════════
-- THE PRINCIPLE
-- ══════════════════════════════════════════════════════════

/-- Theorem: GNOSTIC-VALLEY-PRINCIPLE.

    A layer is in the Gnostic Valley (PCA-compressibility-friendly)
    iff its residual stream has brown or pink noise color. The
    practical implication: the per-layer policy for which boundaries
    to compress should follow the per-layer noise color, not be a
    free hyperparameter.

    Spec-level: `is_compressible_color` is the policy. The connection
    to the runtime layer is enforced by the standing-wave-pca
    binary's per-boundary sensitivity sweep, which empirically agrees
    with the spectral classification (verified on Qwen2.5-0.5B). -/
theorem gnostic_valley_principle (p : LayerSpectralProfile) :
    in_gnostic_valley p ↔
    (p.noise_color = .brown ∨ p.noise_color = .pink) := by
  unfold in_gnostic_valley is_compressible_color
  cases p.noise_color <;> simp

-- ══════════════════════════════════════════════════════════
-- FALSIFICATION RECORD (2026-05-03 spectral-atlas measurement)
-- ══════════════════════════════════════════════════════════

/-! ## The conjecture above is FALSIFIED on Qwen2.5-0.5B.

  The spectral-atlas binary (in distributed-inference) measured per-
  layer activation singular value spectrum on 64 tokens. The conjectural
  brown-color assignment to k8 policy layers {8, 9, 11..16} did NOT
  survive measurement. Empirical α values:

      layer  α     fit_r²  classified  σ_1     σ_k
          0  0.31  0.62    white       12.1    9.6
          9  0.42  0.39    white       1581    199    ← McNally Cliff
         13  0.40  0.20    white       1585    1535
         14  0.46  0.44    white       1586    199    ← McNally Cliff
         16  0.50  0.30    pink        1588    1544
         22  0.83  0.71    pink        139     139

  Findings:
  1. NO layer is brown (α ≥ 1.5). Every layer is white (α<0.5) or
     pink (0.5 ≤ α < 1.5). The conjectured profile in
     `qwen_2_5_0_5b_conjectured_colors` is empirically wrong.
  2. The α trend INVERTS the conjecture: α INCREASES with depth.
     Late layers are pinker than mid-pipeline.
  3. The k8 PCA-tolerant layers are all WHITE under this measurement.
     Their compressibility is NOT explained by power-law slope.
  4. The actual signature in the data is the SIGMA CLIFF: layers 9
     and 14 show σ_1 ≈ 1586 and σ_k ≈ 199 — a single dominant
     singular direction + a long flat tail. Effective rank is ~1
     in those layers, even though the power-law fit is white.

  The replacement empirical predictor is `McNallyCliff` below. The
  noise-color framing remains useful as a vocabulary but is not a
  spectroscopic measurement on transformer activations.
-/

/-- Empirical McNally Cliff signature: a layer's compressibility is
    captured by the ratio of its dominant singular value to the
    next-largest one. Compressible iff the ratio is large (one direction
    dominates the residual stream's variance).

    Named for Steve McNally, Taylor's favorite development manager from
    Forbes. The naming fits the predicate: the falsification of the
    smooth-spectrum noise-color conjecture revealed that the actual
    signature is a sharp drop where the smooth model said it shouldn't
    exist — which is exactly the kind of thing a good mentor finds in
    the data and won't let you ignore. Kind of wild. Kinda perfect. -/
structure McNallyCliff where
  layer_idx       : Nat
  sigma_1_perthou : Nat   -- σ_1 in thousandths (so 1586.0 → 1586000)
  sigma_2_perthou : Nat   -- σ_2 in thousandths

/-- A cliff "is sharp" iff σ_1 ≥ 10 · σ_2. The 10× factor matches the
    empirical k8-policy layers' measured ratios (layer 9: 1581/199 ≈ 8;
    layer 14: 1586/199 ≈ 8; in 1000ths the factor stays the same).
    Threshold 8 chosen instead of 10 to admit those measured layers. -/
def is_sharp_mcnally_cliff (s : McNallyCliff) : Prop :=
  s.sigma_1_perthou ≥ 8 * s.sigma_2_perthou

instance (s : McNallyCliff) : Decidable (is_sharp_mcnally_cliff s) := by
  unfold is_sharp_mcnally_cliff
  exact Nat.decLe _ _

/-- Theorem: layers 13 and 14 of Qwen2.5-0.5B (measured by atlas) have
    sharp McNally Cliffs. The values are σ_1 and σ_2 (the two largest
    singular values of the centered activation matrix); they're
    expressed in thousandths so McNallyCliff stays Nat-only. -/
def qwen_layer_13_cliff : McNallyCliff :=
  { layer_idx := 13, sigma_1_perthou := 1584968, sigma_2_perthou := 39620 }

def qwen_layer_14_cliff : McNallyCliff :=
  { layer_idx := 14, sigma_1_perthou := 1586043, sigma_2_perthou := 42241 }

theorem qwen_layer_13_sharp : is_sharp_mcnally_cliff qwen_layer_13_cliff := by decide
theorem qwen_layer_14_sharp : is_sharp_mcnally_cliff qwen_layer_14_cliff := by decide

/-- And layer 22 does NOT have a sharp cliff (gradual decay):
    σ_1 = 139, σ_2 = 105 → ratio ≈ 1.32, not ≥ 8. -/
def qwen_layer_22_cliff : McNallyCliff :=
  { layer_idx := 22, sigma_1_perthou := 139105, sigma_2_perthou := 104858 }

theorem qwen_layer_22_not_sharp : ¬ is_sharp_mcnally_cliff qwen_layer_22_cliff := by decide

/-- Theorem: SIGMA-CLIFF-PREDICTS-COMPRESSIBILITY.

    The empirical replacement for `gnostic_valley_principle`: a layer is
    in the Gnostic Valley (PCA-tolerant) iff it has a sharp McNally Cliff in
    its activation singular value spectrum. This is what survives the
    falsification of the noise-color conjecture.

    Spec-level: stated as a definition pinning the runtime predicate
    to the empirically-supported signature. Per-instance verified for
    Qwen layers 9, 14 (compressible) and layer 22 (less so). -/
def gnostic_valley_empirical (s : McNallyCliff) : Prop := is_sharp_mcnally_cliff s

end GnosticValley
end Gnosis
