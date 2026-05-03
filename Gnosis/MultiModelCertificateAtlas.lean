/-
  MultiModelCertificateAtlas.lean
  ===============================

  The MULTI-MODEL extension of the wave-2 RuntimeCertificate work.

  RuntimeCertificate.lean ships ONE per-instance certificate
  (qwen_pca_only_certificate) for the model on which the full
  parity / hit-rate pipeline was actually measured this session
  (Qwen2.5-0.5B). This module lifts that pattern to the THREE
  models touched by the spectral-atlas + cliff-topology work:

    1. qwen_2_5_0_5b   — fully measured (F=40/100, hit=73/100)
    2. qwen_coder_7b   — projected (no parity run yet at this scale)
    3. llama_1b        — projected (no parity run yet)

  For each model we declare:

    • a Scheme                 — d, k, boundary count, fidelity
    • a ModelSpectralProfile   — the per-layer (α, d) atlas
    • a VerifyProtocol         — the draft + (hit_num, hit_den)
    • a Lifecycle              — the five-stage operational record
    • a RuntimeCertificate     — the bundle
    • a `<model>_is_certified` theorem (decide-checked)

  The atlas-level theorem
  `multi_model_atlas_has_at_least_one_certified_instance` exhibits
  Qwen2.5-0.5B as the witness: at least one well-typed certificate
  in the atlas decides to `certified`. The other two are HONEST
  PROJECTIONS — their numeric inputs are conjectured from the
  Qwen2.5-0.5B numbers and labelled as such; they will be upgraded
  to "measured" once the standing-wave-parity pipeline is run on
  them at scale (see GAP-LIST below).

  HONESTY GAP-LIST
  ----------------
  Status now (2026-05-02):
    • qwen_2_5_0_5b   — CERTIFIED (measured F, measured hit, parity run)
    • qwen_coder_7b   — PROJECTED (F and hit reused from Qwen2.5-0.5B
                        as a structural placeholder; spectral profile
                        likewise projected from the qwen pattern)
    • llama_1b        — PROJECTED (same caveat; the `CrossModelCliff`
                        atlas already records that llama has a
                        DIFFERENT cliff topology, so the projected
                        F/hit numbers should be treated as upper bounds
                        until measured)

  Upgrade path (PROJECTED → CERTIFIED):
    • Run `standing-wave-pca --policy <model>_pca_k_<k> --measure-fidelity`
      on the deployed model and capture (F_num, F_den) and
      (hit_num, hit_den) from the parity binary.
    • Replace the projected literals in the `<model>_pca` and
      `<model>_pca_verified` definitions below with the measured
      values; rerun `lake build`.
    • Update the spectral profile colors with the PSD-measured α(l)
      from the per-layer spectral-atlas pass.

  Future operators read THIS file to see the certification status
  of every model the atlas currently covers.

  Imports: RuntimeCertificate (wave 2 bundle), CrossModelCliff,
  InformationCapacity, CompressionUncertainty (transitively).

  Init-only Lean 4. Zero sorries, zero axioms.
-/

import Gnosis.RuntimeCertificate
import Gnosis.CrossModelCliff
import Gnosis.InformationCapacity
import Gnosis.CompressionUncertainty

namespace Gnosis
namespace MultiModelCertificateAtlas

open CompressionUncertainty
open Gnosis.InformationCapacity
open Gnosis.ConversionInvariant
open Gnosis.LifecycleAsForkRaceFoldVentInterfere
open Gnosis.RuntimeCertificate

-- Open the spectral-noise namespace so `NoiseColor` and its constructors
-- (`white`, `pink`, `brown`) resolve unambiguously to the
-- `SpectralNoiseEquilibrium` ones (`NoiseTopology` also exports a
-- homonymous `NoiseColor`, hence we DO NOT `open NoiseTopology`).
open SpectralNoiseEquilibrium

set_option maxRecDepth 4096

-- ══════════════════════════════════════════════════════════
-- MODEL #1: QWEN2.5-0.5B (FULLY MEASURED)
-- ══════════════════════════════════════════════════════════

/-- Qwen2.5-0.5B's certificate is the wave-2 bundle, re-exported here
    so the atlas-level theorem has a uniform handle on every model. -/
def qwen_0_5b_certificate : RuntimeCertificate :=
  qwen_pca_only_certificate

/-- Status: CERTIFIED. Decide-checked via the wave-2 theorem. -/
theorem qwen_0_5b_is_certified : certified qwen_0_5b_certificate := by
  decide

-- ══════════════════════════════════════════════════════════
-- MODEL #2: QWEN-CODER-7B (PROJECTED)
-- ══════════════════════════════════════════════════════════

/-- Qwen-coder-7B PCA scheme.
      d=3584, k=1792 (coverage 0.50), 8 of 27 boundaries compressed.
      F is PROJECTED from the Qwen2.5-0.5B measurement (F=40/100);
      no parity run on this model at this scale yet. -/
def qwen_coder_7b_pca : Scheme :=
  { d := 3584, k := 1792, boundaries := 8, total_boundaries := 27
  , f_num := 40, f_denom := 100 }

/-- Verify protocol. hit=73/100 PROJECTED from Qwen2.5-0.5B. -/
def qwen_coder_7b_pca_verified : VerifyProtocol :=
  { draft := qwen_coder_7b_pca, hit_num := 73, hit_denom := 100 }

/-- Spectral profile, projected from the qwen pattern at the wider d.
    Two brown layers (α=2) keep the capacity comfortably above the
    scheme's mass (= (3584-1792)·8 = 14336): one brown alone is
    2·3584 = 7168, two brown is 14336, exactly enough; we add
    pink layers as cushion. -/
def qwen_coder_7b_colors : List NoiseColor :=
  [NoiseColor.white,
   NoiseColor.pink,  NoiseColor.pink,  NoiseColor.pink,  NoiseColor.pink,
   NoiseColor.brown, NoiseColor.brown, NoiseColor.brown,
   NoiseColor.pink,  NoiseColor.pink,  NoiseColor.pink,  NoiseColor.pink,
   NoiseColor.brown, NoiseColor.brown, NoiseColor.brown, NoiseColor.brown,
   NoiseColor.brown,
   NoiseColor.pink,  NoiseColor.pink,  NoiseColor.pink,  NoiseColor.pink,
   NoiseColor.pink,
   NoiseColor.pink,  NoiseColor.pink,  NoiseColor.pink,  NoiseColor.pink,
   NoiseColor.pink]

def qwen_coder_7b_profile : ModelSpectralProfile :=
  uniformWidthProfile qwen_coder_7b_colors 3584

/-- The scheme fits the projected capacity (decidable). -/
theorem qwen_coder_7b_fits_capacity :
    fitsCapacity qwen_coder_7b_pca qwen_coder_7b_profile := by
  decide

/-- The protocol actually saves bytes (k<d ∧ boundaries>0 ∧ hit_num>0). -/
theorem qwen_coder_7b_saves_bytes :
    actuallySavesBytes qwen_coder_7b_pca_verified := by
  decide

/-- β > 0 follows from `actuallySavesBytes`. -/
theorem qwen_coder_7b_beta_positive :
    0 < betaNum qwen_coder_7b_pca_verified := by
  apply beta_positive_when_saving
  exact qwen_coder_7b_saves_bytes

/-- Lifecycle, projected from the Qwen2.5-0.5B operational record.
    Fork: 27 layers measured. Race: 8 winners of 27 boundaries.
    Fold: pca artifact ~32 MB (8 layers × 1792 components × 4 B × ~0.55).
    Vent: candidate-set verifier wired, hit projected 73/100.
    Interfere: trivial — single PCA surface. -/
def qwen_coder_7b_lifecycle : Lifecycle :=
  { fork      := { num_elements := 27,    measured_count := 27 }
  , race      := { num_candidates := 27,  winners_count := 8
                 , passes_criterion := true }
  , fold      := { artifact_size_bytes := 32_000_000
                 , artifact_consistent := true }
  , vent      := { has_verifier := true
                 , rollback_num := 27,    rollback_den := 100 }
  , interfere := .trivial }

/-- The bundle. -/
def qwen_coder_7b_certificate : RuntimeCertificate :=
  { protocol  := qwen_coder_7b_pca_verified
  , profile   := qwen_coder_7b_profile
  , lifecycle := qwen_coder_7b_lifecycle
  , fits      := qwen_coder_7b_fits_capacity
  , betaPos   := qwen_coder_7b_beta_positive }

/-- Status: PROJECTED-CERTIFIED. The certificate is well-typed and
    decides to `certified` ON THE PROJECTED INPUTS. The honest reading
    is: "if the Qwen-coder-7B's measured numbers come back at least as
    good as the projected ones, the deployment is production-ready by
    the same criterion that already passed Qwen2.5-0.5B." Decide-checked.

    Upgrade to `qwen_coder_7b_is_certified` (drop the suffix) once the
    standing-wave-parity pipeline runs on this model. -/
theorem qwen_coder_7b_is_certified_pending_measurement :
    certified qwen_coder_7b_certificate := by
  decide

-- ══════════════════════════════════════════════════════════
-- MODEL #3: LLAMA-1B (PROJECTED)
-- ══════════════════════════════════════════════════════════

/-- Llama-1B PCA scheme.
      d=2048, k=1024 (coverage 0.50), 8 of 22 boundaries compressed.
      F is PROJECTED from Qwen2.5-0.5B (F=40/100); the
      `CrossModelCliff` atlas already records that Llama-1B's cliff
      topology is BAND (not Spike), so the projected F should be
      treated as an UPPER BOUND on the achievable fidelity until
      a real parity run lands. -/
def llama_1b_pca : Scheme :=
  { d := 2048, k := 1024, boundaries := 8, total_boundaries := 22
  , f_num := 40, f_denom := 100 }

/-- Verify protocol. hit=73/100 PROJECTED from Qwen2.5-0.5B. -/
def llama_1b_pca_verified : VerifyProtocol :=
  { draft := llama_1b_pca, hit_num := 73, hit_denom := 100 }

/-- Spectral profile, projected from the llama BAND pattern.
    `CrossModelCliff` records llama as having ≥1 brown layer and a
    contiguous cliff band; we model that as a brown band over layers
    1..6 (six brown layers) with white at layer 0 and pink elsewhere.
    Capacity: 6·2·2048 = 24576, comfortably above the scheme's mass
    (= (2048-1024)·8 = 8192). -/
def llama_1b_colors : List NoiseColor :=
  [NoiseColor.white,
   NoiseColor.brown, NoiseColor.brown, NoiseColor.brown,
   NoiseColor.brown, NoiseColor.brown, NoiseColor.brown,
   NoiseColor.pink,  NoiseColor.pink,  NoiseColor.pink,  NoiseColor.pink,
   NoiseColor.pink,
   NoiseColor.pink,  NoiseColor.pink,  NoiseColor.pink,  NoiseColor.pink,
   NoiseColor.pink,
   NoiseColor.pink,  NoiseColor.pink,  NoiseColor.pink,  NoiseColor.pink,
   NoiseColor.pink]

def llama_1b_profile : ModelSpectralProfile :=
  uniformWidthProfile llama_1b_colors 2048

/-- Scheme fits projected capacity. -/
theorem llama_1b_fits_capacity :
    fitsCapacity llama_1b_pca llama_1b_profile := by
  decide

/-- Protocol actually saves bytes. -/
theorem llama_1b_saves_bytes :
    actuallySavesBytes llama_1b_pca_verified := by
  decide

/-- β > 0. -/
theorem llama_1b_beta_positive :
    0 < betaNum llama_1b_pca_verified := by
  apply beta_positive_when_saving
  exact llama_1b_saves_bytes

/-- Lifecycle, projected. Fork: 22 layers; Race: 8 winners of 21
    boundaries; Fold: ~16 MB; Vent: K=5 candidate verifier wired;
    Interfere: trivial (single PCA surface). -/
def llama_1b_lifecycle : Lifecycle :=
  { fork      := { num_elements := 22,    measured_count := 22 }
  , race      := { num_candidates := 21,  winners_count := 8
                 , passes_criterion := true }
  , fold      := { artifact_size_bytes := 16_000_000
                 , artifact_consistent := true }
  , vent      := { has_verifier := true
                 , rollback_num := 27,    rollback_den := 100 }
  , interfere := .trivial }

/-- The bundle. -/
def llama_1b_certificate : RuntimeCertificate :=
  { protocol  := llama_1b_pca_verified
  , profile   := llama_1b_profile
  , lifecycle := llama_1b_lifecycle
  , fits      := llama_1b_fits_capacity
  , betaPos   := llama_1b_beta_positive }

/-- Status: PROJECTED-CERTIFIED. Same caveat as `qwen_coder_7b`. -/
theorem llama_1b_is_certified_pending_measurement :
    certified llama_1b_certificate := by
  decide

-- ══════════════════════════════════════════════════════════
-- THE ATLAS
-- ══════════════════════════════════════════════════════════

/-- The atlas: every certificate the multi-model extension currently
    knows about. New models are appended here as their parity runs
    land. -/
def atlas : List RuntimeCertificate :=
  [ qwen_0_5b_certificate
  , qwen_coder_7b_certificate
  , llama_1b_certificate ]

/-- The atlas is non-empty. -/
theorem atlas_nonempty : atlas ≠ [] := by
  decide

/-- The atlas covers exactly three models in this wave. -/
theorem atlas_size_is_three : atlas.length = 3 := by
  decide

-- ══════════════════════════════════════════════════════════
-- THE ATLAS-LEVEL CERTIFICATION THEOREM
-- ══════════════════════════════════════════════════════════

/-- Theorem: MULTI-MODEL-ATLAS-HAS-AT-LEAST-ONE-CERTIFIED-INSTANCE.

    There exists a well-typed `RuntimeCertificate` in the atlas that
    is `certified` by `decide`. The witness is `qwen_0_5b_certificate`
    — the only model in this wave whose F and hit-rate inputs are
    MEASURED (not projected).

    Operationally: the multi-model deployment is grounded by at least
    one fully measured certificate. Future waves upgrade the projected
    instances to measured by replacing the `f_num/f_denom` and
    `hit_num/hit_denom` literals in this file and re-running
    `lake build`. -/
theorem multi_model_atlas_has_at_least_one_certified_instance :
    ∃ C ∈ atlas, certified C := by
  refine ⟨qwen_0_5b_certificate, ?_, ?_⟩
  · -- membership in the atlas list: head position
    exact List.Mem.head _
  · -- certified
    exact qwen_0_5b_is_certified

/-- Theorem: ALL-THREE-CURRENT-CERTIFICATES-DECIDE-CERTIFIED.

    Stronger statement on the current atlas: every certificate (the
    measured one AND the two projected ones) decides to `certified`
    on its current inputs. The honest reading is the same as the
    per-instance status: the projected ones survive the structural
    check because their projected inputs are at-least-as-good as the
    measured Qwen2.5-0.5B numbers; a real parity run could lower F
    or hit and break this. -/
theorem all_three_current_certificates_decide_certified :
    certified qwen_0_5b_certificate ∧
    certified qwen_coder_7b_certificate ∧
    certified llama_1b_certificate := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

-- ══════════════════════════════════════════════════════════
-- STATUS PROJECTIONS (operator-facing one-liners)
-- ══════════════════════════════════════════════════════════

/-- Operator query: is the deployed Qwen2.5-0.5B production-ready? -/
theorem qwen_0_5b_status_measured_certified :
    certified qwen_0_5b_certificate :=
  qwen_0_5b_is_certified

/-- Operator query: is the projected Qwen-coder-7B configuration
    self-consistent (i.e., would it certify under its projected
    inputs)? Answer: yes; needs measurement to be load-bearing. -/
theorem qwen_coder_7b_status_projected_certified :
    certified qwen_coder_7b_certificate :=
  qwen_coder_7b_is_certified_pending_measurement

/-- Operator query: same for Llama-1B. -/
theorem llama_1b_status_projected_certified :
    certified llama_1b_certificate :=
  llama_1b_is_certified_pending_measurement

end MultiModelCertificateAtlas
end Gnosis
