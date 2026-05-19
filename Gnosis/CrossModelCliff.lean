import Gnosis.GnosticValley

/-
  CrossModelCliff.lean
  ====================

  Cross-model formalization of the wave-1 spectral-atlas finding: the
  McNally Cliff phenomenon is REAL across model families, but its exact
  topology is MODEL-SPECIFIC.

  Source data (`docs/spectral-atlas-llama-1b.md`, run 2026-05-02):

  - Llama-1B (TinyLlama 1.1B class, 22 layers):
      * brown spectrum at layer 1 (α=1.78, r²=0.52)
      * contiguous BAND of sharp DC-cliffs in layers 2..7 with ratios
        53 → 42 → 35 → 29 → 23 → 8 — monotonically softening
      * cliff dissolves toward the output (layers 17..20: ratios <7)
  - Qwen2.5-0.5B (24 layers, prior wave):
      * NO brown layers anywhere
      * isolated SPIKES at layers 9 / 13 / 14 with ratios 8 / 40 / 38
      * mostly white, α increasing toward pink at the tail (layer 22
        α≈0.83 / pink)

  These two empirical instances exhibit categorically different cliff
  topologies: one is a contiguous band, the other a discrete spike set.
  Both contain sharp McNally Cliffs. Therefore the McNally Cliff law
  CANNOT be stated as a single universal layer-shape across architectures
  — it must be parameterized by model family.

  This module formalizes that falsification cleanly: it defines the four
  possible cliff topologies (Spike / Band / Mixed / None), records the
  two measured ModelCliffProfiles, and proves by `decide` that they
  disagree on every diagnostic that matters.

  Init-only Lean 4. Imports only `Gnosis.GnosticValley`. Zero sorries,
  zero axioms.
-/


namespace Gnosis
namespace CrossModelCliff

-- ══════════════════════════════════════════════════════════
-- CLIFF TOPOLOGY
-- ══════════════════════════════════════════════════════════

/-- The four shapes a model's per-layer McNally-cliff signature can take
    when surveyed across its full depth.

    - `Spike`: cliffs occur at isolated, non-adjacent layers
      (Qwen2.5-0.5B: 9, 13, 14 — gaps in between).
    - `Band` : cliffs form a contiguous range of layer indices
      (Llama-1B: layers 2..7 all sharp).
    - `Mixed`: both an isolated spike and a contiguous band coexist.
    - `None` : no layer crosses the sharp-cliff threshold. -/
inductive CliffTopology
  | Spike
  | Band
  | Mixed
  | None
  deriving DecidableEq, Repr

-- ══════════════════════════════════════════════════════════
-- MODEL CLIFF PROFILE
-- ══════════════════════════════════════════════════════════

/-- Per-model summary of the spectral-atlas measurement. The four fields
    are the minimum needed to distinguish the empirically observed
    Llama-1B and Qwen2.5-0.5B patterns. -/
structure ModelCliffProfile where
  model_name      : String
  num_layers      : Nat
  has_brown_layer : Bool
  cliff_topology  : CliffTopology
  deriving Repr

/-- Equality on profiles is decidable so we can `decide` the
    disagreement theorem at the end of the file. -/
instance : DecidableEq ModelCliffProfile := fun a b => by
  cases a; cases b
  simp [ModelCliffProfile.mk.injEq]
  exact instDecidableAnd

-- ══════════════════════════════════════════════════════════
-- PATTERN PREDICATES
-- ══════════════════════════════════════════════════════════

/-- The "Qwen pattern": no brown layer, cliffs are isolated spikes.
    Layer count is left flexible — what defines the pattern is the
    topology + brown absence, not the depth. -/
def is_qwen_pattern (p : ModelCliffProfile) : Bool :=
  p.has_brown_layer = false ∧ p.cliff_topology = CliffTopology.Spike

/-- The "Llama pattern": at least one brown layer, cliffs form a
    contiguous band. -/
def is_llama_pattern (p : ModelCliffProfile) : Bool :=
  p.has_brown_layer = true ∧ p.cliff_topology = CliffTopology.Band

-- ══════════════════════════════════════════════════════════
-- EMPIRICAL INSTANCES
-- ══════════════════════════════════════════════════════════

/-- Qwen2.5-0.5B as measured in the prior wave (24 layers). No brown
    spectrum at any depth; sharp cliffs at scattered mid-layers
    9 / 13 / 14 → topology = Spike. -/
def qwen_2_5_0_5b_profile : ModelCliffProfile :=
  { model_name      := "Qwen2.5-0.5B"
    num_layers      := 24
    has_brown_layer := false
    cliff_topology  := CliffTopology.Spike }

/-- Llama-1B (TinyLlama 1.1B class) as measured 2026-05-02 (22 layers).
    Brown spectrum at layer 1 (α=1.78); contiguous cliff band in layers
    2..7 → topology = Band. -/
def llama_1b_profile : ModelCliffProfile :=
  { model_name      := "Llama-1B"
    num_layers      := 22
    has_brown_layer := true
    cliff_topology  := CliffTopology.Band }

-- ══════════════════════════════════════════════════════════
-- PER-INSTANCE DIAGNOSTICS (proved by `decide`)
-- ══════════════════════════════════════════════════════════

/-- Qwen's measured topology is Spike. -/
theorem qwen_is_spike_topology :
    qwen_2_5_0_5b_profile.cliff_topology = CliffTopology.Spike := by decide

/-- Llama's measured topology is Band. -/
theorem llama_is_band_topology :
    llama_1b_profile.cliff_topology = CliffTopology.Band := by decide

/-- Qwen has no brown layer in its spectral atlas. -/
theorem qwen_has_no_brown :
    qwen_2_5_0_5b_profile.has_brown_layer = false := by decide

/-- Llama has at least one brown layer (layer 1, α=1.78). -/
theorem llama_has_brown :
    llama_1b_profile.has_brown_layer = true := by decide

/-- The Qwen instance matches the qwen pattern. -/
theorem qwen_matches_qwen_pattern :
    is_qwen_pattern qwen_2_5_0_5b_profile = true := by decide

/-- The Llama instance matches the llama pattern. -/
theorem llama_matches_llama_pattern :
    is_llama_pattern llama_1b_profile = true := by decide

/-- The Qwen instance does NOT match the llama pattern (different
    topology, no brown). -/
theorem qwen_pattern_differs_from_llama_pattern :
    is_llama_pattern qwen_2_5_0_5b_profile = false := by decide

/-- Symmetric statement: the Llama instance does not match the qwen
    pattern. Together with the previous theorem this rules out a single
    pattern covering both architectures. -/
theorem llama_pattern_differs_from_qwen_pattern :
    is_qwen_pattern llama_1b_profile = false := by decide

-- ══════════════════════════════════════════════════════════
-- THE PRINCIPLE
-- ══════════════════════════════════════════════════════════

/-- Theorem: MCNALLY-CLIFF-IS-MODEL-SPECIFIC.

    There exist two well-typed `ModelCliffProfile` values whose cliff
    topologies disagree. Concretely: `qwen_2_5_0_5b_profile` has
    topology `Spike` and `llama_1b_profile` has topology `Band`.

    Spec-level: this is the formal record of the wave-1 falsification.
    A theorist who proposed "every transformer's residual stream
    exhibits the same McNally-cliff layer pattern" is refuted by
    construction — the witness is two empirically measured profiles in
    the same file whose `cliff_topology` fields are provably distinct.

    Implication for the runtime: the per-layer compression policy
    (`k8_policy_layers` in `GnosticValley.lean`) is calibrated to one
    architecture and CANNOT be transported to another without
    re-measurement. The McNally Cliff is a universal phenomenon; the
    schedule of WHERE it lives in the stack is not. -/
theorem mcnally_cliff_is_model_specific :
    ∃ a b : ModelCliffProfile, a.cliff_topology ≠ b.cliff_topology := by
  refine ⟨qwen_2_5_0_5b_profile, llama_1b_profile, ?_⟩
  decide

end CrossModelCliff
end Gnosis
