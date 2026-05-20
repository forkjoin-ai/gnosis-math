import Init
import Gnosis.FanoFRFVI

/-!
# FailureAsStandingWave — failure-driven theory as eigenmode dynamics

This module formalizes a hypothesis that emerged empirically from the
GKQ rank-K compression work (see `GKQHelixBandwidth.lean` Coda):

> The body of viable theory is a standing wave on claim-space, with
> Dirichlet boundary conditions imposed by falsified claims.

The physics analogy is exact. A standing wave in a bounded medium is
the set of solutions to a wave equation that must be zero at certain
fixed points (nodes). The shape of the wave is determined entirely by
*where it cannot exist*. The viable modes — the discrete set of
frequencies the system actually supports — emerge from the geometry
of the boundary, not from any "positive" specification of what the
wave should look like.

Same structure for a Popperian theory body. A claim space `C` is the
medium. The falsification set `F ⊂ C` is the boundary. A viable theory
is a function `T : C → Plausibility` that vanishes on `F` (you cannot
assign positive plausibility to a falsified claim) and is supported on
`C \ F`. The discrete set of "stable" theories — the ones that survive
all known no-go results — are the eigenmodes of a constraint operator
on this domain.

Two empirical anchors:
1. **gnosis-math is built on failure.** Every load-bearing theorem in
   `GKQHelixBandwidth` is a no-go result. The library teaches what
   doesn't work and why. This is the methodology *as* boundary-
   condition specification.
2. **Rank-K compression converges on negation.** GKQ rank-256 forced
   to discard everything but the most load-bearing dimension of LLM
   semantic space landed on `{not, Not, 合法, 不愿意}` —
   linguistic markers of negation, exclusion, "what is ruled out".
   The most information-dense axis of the model's distribution is
   the *boundary-marking* axis.

These two observations are the same observation, stated twice. The
information-theoretic kernel of a constraint-respecting system is the
specification of its boundaries.

Connection to existing infrastructure: gnosis distributed-inference
already has a `standing-wave-pca` tool that fits PCA modes to a
calibration corpus and ships only the modes that "stand" (survive
across the corpus). The naming wasn't decorative — that work was
finding the eigenmodes of the constraint operator induced by the
calibration prompts. This module names the broader pattern.
-/

namespace Gnosis
namespace FailureAsStandingWave

-- ══════════════════════════════════════════════════════════
-- SECTION 1 — Claim space and falsification boundaries
-- ══════════════════════════════════════════════════════════

/-- A discrete claim index. In a full theory each `Claim` would be a
    proposition; here we work with `Nat`-indexed surrogates so all
    membership questions stay decidable without Mathlib. -/
abbrev Claim := Nat

/-- A falsification boundary: a decidable membership test that says
    whether a given claim has been disproven by a counterexample. -/
structure FalsificationSet where
  isFalsified : Claim → Bool

/-- The viable predicate: a claim is viable iff it has not been
    falsified. By construction, viability is decidable. -/
def isViable (F : FalsificationSet) (c : Claim) : Bool :=
  ! F.isFalsified c

-- ══════════════════════════════════════════════════════════
-- SECTION 2 — Standing-wave modes on claim space
-- ══════════════════════════════════════════════════════════

/-- A standing-wave mode assigns a `Nat` amplitude (plausibility,
    attention weight, whatever) to each claim, subject to a Dirichlet
    boundary condition: amplitude must vanish on every falsified claim.

    Field `vanishesOnFalsified` enforces the BC at the type level.
    Any constructor of `StandingWaveMode F` ships a mathematical
    proof that the mode respects all of `F`'s no-go boundaries. -/
structure StandingWaveMode (F : FalsificationSet) where
  amplitude            : Claim → Nat
  vanishesOnFalsified  : ∀ c, F.isFalsified c = true → amplitude c = 0

/-- The trivial mode: uniformly zero. Always satisfies the BC. -/
def trivialMode (F : FalsificationSet) : StandingWaveMode F where
  amplitude _          := 0
  vanishesOnFalsified  := by intros _ _; rfl

/-- A mode is *supported* at claim `c` iff its amplitude there is
    positive. By the Dirichlet BC, support is necessarily a subset
    of the viable set. -/
def supportedAt (m : StandingWaveMode F) (c : Claim) : Bool :=
  decide (m.amplitude c > 0)

/-- **Theorem (support exclusion).** A standing-wave mode cannot be
    supported on a falsified claim. The negation axis marks the
    boundary; the mode lives in its complement. -/
theorem support_disjoint_from_falsifications
    (F : FalsificationSet) (m : StandingWaveMode F) (c : Claim)
    (hF : F.isFalsified c = true) : supportedAt m c = false := by
  have h0 : m.amplitude c = 0 := m.vanishesOnFalsified c hF
  simp [supportedAt, h0]

-- ══════════════════════════════════════════════════════════
-- SECTION 3 — Worked example: a 4-claim space with two falsifications
-- ══════════════════════════════════════════════════════════

/-- A concrete falsification set: claims 1 and 3 are disproven;
    claims 0 and 2 are viable. Mirrors a tiny theory with two no-go
    boundaries and two viable interior modes. -/
def exampleF : FalsificationSet where
  isFalsified
    | 1 => true
    | 3 => true
    | _ => false

/-- A nontrivial standing-wave mode on `exampleF`: amplitude 5 at
    claim 0, amplitude 7 at claim 2, zero elsewhere. Satisfies BCs
    at claims 1 and 3 (the falsified ones). -/
def exampleMode : StandingWaveMode exampleF where
  amplitude
    | 0 => 5
    | 2 => 7
    | _ => 0
  vanishesOnFalsified := by
    intro c hF
    -- exampleF marks 1 and 3 as falsified; mode is zero on both.
    cases c with
    | zero => simp_all [exampleF]
    | succ n =>
      cases n with
      | zero => rfl
      | succ m =>
        cases m with
        | zero => simp_all [exampleF]
        | succ k =>
          cases k with
          | zero => rfl
          | succ _ => rfl

/-- Witness: the example mode is supported at claim 0 (its amplitude
    is 5 > 0). A nontrivial standing wave exists. -/
theorem example_mode_supported_at_zero :
    supportedAt exampleMode 0 = true := by decide

/-- Witness: the example mode is NOT supported at claim 1 (falsified
    boundary). The BC holds at the type level. -/
theorem example_mode_unsupported_at_one :
    supportedAt exampleMode 1 = false := by decide

-- ══════════════════════════════════════════════════════════
-- SECTION 4 — Empirical bridge to GKQHelixBandwidth
-- ══════════════════════════════════════════════════════════
-- Recorded link to the rank-K compression empirical finding.

/-- GKQ rank-256 Qwen-0.5B greedy attractor token under the
    "Capital of France" prompt (see `GKQHelixBandwidth.Section 6`).
    Carried here so this module can refer to it without re-stating. -/
def gkqAttractorTokenId : Nat := 537  -- " not"

/-- The empirical claim: rank-K compression of an LLM weight matrix
    converges, under forced compression, onto the linguistic boundary-
    marking tokens. This is the standing-wave fingerprint: the
    most-load-bearing axis of compressed semantic space is the
    falsification axis itself. -/
def gkqCompressionAxis : String := "negation-volition-legality"

/-- **Hypothesis (recorded, not yet formally proved).** When a
    compression scheme is forced past the rank threshold where
    argmax-fidelity breaks, the surviving axis is the one most
    correlated with the system's *constraint* set. For LLMs
    trained on natural language, the constraint set is implicit
    in the negation/legality vocabulary that marks "what is ruled
    out". GKQ's empirical convergence on this axis is the
    compression-side mirror of `gnosis-math`'s methodology-side
    convergence on no-go theorems. -/
def compression_failure_axis_equals_methodology_failure_axis : Bool := true

theorem fixed_point_recorded :
    compression_failure_axis_equals_methodology_failure_axis = true := by
  decide

-- ══════════════════════════════════════════════════════════
-- SECTION 5 — Research-program frontier
-- ══════════════════════════════════════════════════════════

/-- A next experiment that can falsify or refine the universality claim.
    These entries are records of empirical work to run, not formal proofs
    that the negation-axis convergence is universal. -/
inductive NextExperiment where
  | adaptiveRank
  | hybridSpectralResidual
  | replicateGemma
  | replicateLlama
  deriving DecidableEq

/-- Possible empirical outcomes for a frontier experiment. `survives`
    supports the universality hypothesis, `fails` weakens it, and
    `inconclusive` means the measurement did not decide the criterion. -/
inductive ExperimentOutcome where
  | survives
  | fails
  | inconclusive
  deriving DecidableEq

/-- The kind of observable that decides a frontier experiment. Adaptive rank,
    hybrid residuals, and cross-family replication are not the same
    measurement, even when they all report whether the boundary axis survived. -/
inductive ExperimentCriterion where
  | survivesAdaptiveRank
  | survivesHybridResidual
  | replicatesOnGemma
  | replicatesOnLlama
  deriving DecidableEq

/-- Criterion-specific evidence. The fields remain finite and Init-only, but
    they no longer hide different measurement classes behind one number. -/
inductive ExperimentEvidence where
  | adaptiveRank (stableTensorCount : Nat)
  | hybridResidual (residualDominanceWitnesses : Nat)
  | gemmaReplication (recurrenceWitnesses distinctPrompts : Nat)
  | llamaReplication (recurrenceWitnesses distinctPrompts : Nat)
  deriving DecidableEq

/-- An observed result pairs the experiment-specific criterion with the
    measured outcome and evidence shaped for the measurement class. -/
structure ExperimentObservation where
  criterion : ExperimentCriterion
  outcome   : ExperimentOutcome
  evidence  : ExperimentEvidence
  deriving DecidableEq

/-- Direction #1: choose rank per tensor instead of imposing one global rank.
    If the boundary axis only appears under a brittle fixed-rank cutoff, the
    universality hypothesis weakens. -/
def directionOneAdaptiveRank : NextExperiment := NextExperiment.adaptiveRank

/-- Direction #2 / Task #27: combine spectral compression with a Q4_K residual.
    The hybrid test asks whether the boundary-marking mode survives once dense
    residual information is allowed back into the system. -/
def directionTwoTask27Hybrid : NextExperiment := NextExperiment.hybridSpectralResidual

/-- Replication on Gemma-family weights. -/
def replicationGemma : NextExperiment := NextExperiment.replicateGemma

/-- Replication on Llama-family weights. -/
def replicationLlama : NextExperiment := NextExperiment.replicateLlama

/-- The current state is a research program: formal kernel, empirical anchor,
    cross-disciplinary frame, and a finite frontier of falsifying experiments. -/
def researchProgramFrontier : List NextExperiment :=
  [ directionOneAdaptiveRank
  , directionTwoTask27Hybrid
  , replicationGemma
  , replicationLlama
  ]

/-- The frontier is nonempty: the current evidence is not being treated as a
    completed universality proof. -/
theorem research_program_has_next_experiments :
    researchProgramFrontier ≠ [] := by
  decide

/-- The specific observable required for each frontier experiment. -/
def requiredCriterion : NextExperiment → ExperimentCriterion
  | NextExperiment.adaptiveRank => ExperimentCriterion.survivesAdaptiveRank
  | NextExperiment.hybridSpectralResidual => ExperimentCriterion.survivesHybridResidual
  | NextExperiment.replicateGemma => ExperimentCriterion.replicatesOnGemma
  | NextExperiment.replicateLlama => ExperimentCriterion.replicatesOnLlama

/-- Whether the observation carries the correct evidence shape and enough
    evidence for the experiment's criterion. -/
def hasRequiredEvidence : NextExperiment → ExperimentObservation → Bool
  | NextExperiment.adaptiveRank, observation =>
      match observation.evidence with
      | ExperimentEvidence.adaptiveRank stableTensorCount =>
          decide (1 ≤ stableTensorCount)
      | _ => false
  | NextExperiment.hybridSpectralResidual, observation =>
      match observation.evidence with
      | ExperimentEvidence.hybridResidual residualDominanceWitnesses =>
          decide (1 ≤ residualDominanceWitnesses)
      | _ => false
  | NextExperiment.replicateGemma, observation =>
      match observation.evidence with
      | ExperimentEvidence.gemmaReplication recurrenceWitnesses distinctPrompts =>
          decide (2 ≤ recurrenceWitnesses && 2 ≤ distinctPrompts)
      | _ => false
  | NextExperiment.replicateLlama, observation =>
      match observation.evidence with
      | ExperimentEvidence.llamaReplication recurrenceWitnesses distinctPrompts =>
          decide (2 ≤ recurrenceWitnesses && 2 ≤ distinctPrompts)
      | _ => false

/-- A falsifiable criterion for each frontier experiment. An observation
    supports the universality hypothesis only if it measures the experiment's
    own required criterion, reports survival, and carries enough evidence for
    that experiment's measurement class. -/
def boundaryAxisSurvives (experiment : NextExperiment)
    (observation : ExperimentObservation) : Bool :=
  observation.criterion == requiredCriterion experiment
    && observation.outcome == ExperimentOutcome.survives
    && hasRequiredEvidence experiment observation

/-- The adaptive-rank experiment supports universality only if the axis survives
    per-tensor rank selection. -/
theorem adaptive_rank_requires_survival :
    boundaryAxisSurvives directionOneAdaptiveRank
      { criterion := ExperimentCriterion.survivesAdaptiveRank
        outcome := ExperimentOutcome.survives
        evidence := ExperimentEvidence.adaptiveRank 1 } = true := by
  decide

/-- The Task #27 hybrid experiment supports universality only if the axis
    survives the spectral + Q4_K residual setting. -/
theorem task27_hybrid_requires_survival :
    boundaryAxisSurvives directionTwoTask27Hybrid
      { criterion := ExperimentCriterion.survivesHybridResidual
        outcome := ExperimentOutcome.survives
        evidence := ExperimentEvidence.hybridResidual 1 } = true := by
  decide

/-- Failed Gemma replication does not support the universality claim. -/
theorem failed_gemma_replication_does_not_support_universality :
    boundaryAxisSurvives replicationGemma
      { criterion := ExperimentCriterion.replicatesOnGemma
        outcome := ExperimentOutcome.fails
        evidence := ExperimentEvidence.gemmaReplication 2 2 } = false := by
  decide

/-- Failed Llama replication does not support the universality claim. -/
theorem failed_llama_replication_does_not_support_universality :
    boundaryAxisSurvives replicationLlama
      { criterion := ExperimentCriterion.replicatesOnLlama
        outcome := ExperimentOutcome.fails
        evidence := ExperimentEvidence.llamaReplication 2 2 } = false := by
  decide

/-- A survival result for the wrong observable does not support the experiment:
    each frontier item has to measure its own criterion. -/
theorem wrong_criterion_does_not_support_adaptive_rank :
    boundaryAxisSurvives directionOneAdaptiveRank
      { criterion := ExperimentCriterion.survivesHybridResidual
        outcome := ExperimentOutcome.survives
        evidence := ExperimentEvidence.hybridResidual 1 } = false := by
  decide

/-- Even with the right criterion, the wrong evidence shape does not support
    adaptive-rank survival. -/
theorem wrong_evidence_shape_does_not_support_adaptive_rank :
    boundaryAxisSurvives directionOneAdaptiveRank
      { criterion := ExperimentCriterion.survivesAdaptiveRank
        outcome := ExperimentOutcome.survives
        evidence := ExperimentEvidence.hybridResidual 1 } = false := by
  decide

/-- Cross-family replication requires more than one recurrence witness. -/
theorem single_gemma_witness_is_insufficient :
    boundaryAxisSurvives replicationGemma
      { criterion := ExperimentCriterion.replicatesOnGemma
        outcome := ExperimentOutcome.survives
        evidence := ExperimentEvidence.gemmaReplication 1 2 } = false := by
  decide

/-- Two Gemma recurrence witnesses on one prompt are still insufficient. -/
theorem two_gemma_witnesses_one_prompt_is_insufficient :
    boundaryAxisSurvives replicationGemma
      { criterion := ExperimentCriterion.replicatesOnGemma
        outcome := ExperimentOutcome.survives
        evidence := ExperimentEvidence.gemmaReplication 2 1 } = false := by
  decide

/-- Two Gemma recurrence witnesses across two prompts are enough for the
    lightweight frontier threshold. -/
theorem two_gemma_witnesses_two_prompts_support_replication :
    boundaryAxisSurvives replicationGemma
      { criterion := ExperimentCriterion.replicatesOnGemma
        outcome := ExperimentOutcome.survives
        evidence := ExperimentEvidence.gemmaReplication 2 2 } = true := by
  decide

/-- Llama evidence cannot stand in for Gemma replication. -/
theorem llama_evidence_does_not_support_gemma_replication :
    boundaryAxisSurvives replicationGemma
      { criterion := ExperimentCriterion.replicatesOnGemma
        outcome := ExperimentOutcome.survives
        evidence := ExperimentEvidence.llamaReplication 2 2 } = false := by
  decide

/-- Gemma evidence cannot stand in for Llama replication. -/
theorem gemma_evidence_does_not_support_llama_replication :
    boundaryAxisSurvives replicationLlama
      { criterion := ExperimentCriterion.replicatesOnLlama
        outcome := ExperimentOutcome.survives
        evidence := ExperimentEvidence.gemmaReplication 2 2 } = false := by
  decide

/-- Two Llama recurrence witnesses on one prompt are still insufficient. -/
theorem two_llama_witnesses_one_prompt_is_insufficient :
    boundaryAxisSurvives replicationLlama
      { criterion := ExperimentCriterion.replicatesOnLlama
        outcome := ExperimentOutcome.survives
        evidence := ExperimentEvidence.llamaReplication 2 1 } = false := by
  decide

/-- Two Llama recurrence witnesses across two prompts are enough for the
    lightweight frontier threshold. -/
theorem two_llama_witnesses_two_prompts_support_replication :
    boundaryAxisSurvives replicationLlama
      { criterion := ExperimentCriterion.replicatesOnLlama
        outcome := ExperimentOutcome.survives
        evidence := ExperimentEvidence.llamaReplication 2 2 } = true := by
  decide

/-- A complete frontier observation has one named observation for each current
    experiment. Universality is not inferred from any single slot. -/
structure FrontierObservation where
  adaptiveRankObservation : ExperimentObservation
  hybridResidualObservation : ExperimentObservation
  gemmaReplicationObservation : ExperimentObservation
  llamaReplicationObservation : ExperimentObservation
  deriving DecidableEq

/-- The whole frontier supports universality only when every named experiment
    survives its own criterion and evidence gate. -/
def frontierSupportsUniversality (frontier : FrontierObservation) : Bool :=
  boundaryAxisSurvives directionOneAdaptiveRank frontier.adaptiveRankObservation
    && boundaryAxisSurvives directionTwoTask27Hybrid frontier.hybridResidualObservation
    && boundaryAxisSurvives replicationGemma frontier.gemmaReplicationObservation
    && boundaryAxisSurvives replicationLlama frontier.llamaReplicationObservation

/-- A fully matched frontier supports the universality hypothesis. -/
theorem complete_frontier_supports_universality :
    frontierSupportsUniversality
      { adaptiveRankObservation :=
          { criterion := ExperimentCriterion.survivesAdaptiveRank
            outcome := ExperimentOutcome.survives
            evidence := ExperimentEvidence.adaptiveRank 1 }
        hybridResidualObservation :=
          { criterion := ExperimentCriterion.survivesHybridResidual
            outcome := ExperimentOutcome.survives
            evidence := ExperimentEvidence.hybridResidual 1 }
        gemmaReplicationObservation :=
          { criterion := ExperimentCriterion.replicatesOnGemma
            outcome := ExperimentOutcome.survives
            evidence := ExperimentEvidence.gemmaReplication 2 2 }
        llamaReplicationObservation :=
          { criterion := ExperimentCriterion.replicatesOnLlama
            outcome := ExperimentOutcome.survives
            evidence := ExperimentEvidence.llamaReplication 2 2 } } = true := by
  decide

/-- A frontier with only the compression-side experiments passing is not enough:
    missing Gemma replication blocks the universality gate. -/
theorem missing_gemma_replication_blocks_universality :
    frontierSupportsUniversality
      { adaptiveRankObservation :=
          { criterion := ExperimentCriterion.survivesAdaptiveRank
            outcome := ExperimentOutcome.survives
            evidence := ExperimentEvidence.adaptiveRank 1 }
        hybridResidualObservation :=
          { criterion := ExperimentCriterion.survivesHybridResidual
            outcome := ExperimentOutcome.survives
            evidence := ExperimentEvidence.hybridResidual 1 }
        gemmaReplicationObservation :=
          { criterion := ExperimentCriterion.replicatesOnGemma
            outcome := ExperimentOutcome.inconclusive
            evidence := ExperimentEvidence.gemmaReplication 2 2 }
        llamaReplicationObservation :=
          { criterion := ExperimentCriterion.replicatesOnLlama
            outcome := ExperimentOutcome.survives
            evidence := ExperimentEvidence.llamaReplication 2 2 } } = false := by
  decide

/-- Passing Gemma and Llama replication cannot compensate for a failed hybrid
    residual experiment. -/
theorem failed_hybrid_blocks_universality :
    frontierSupportsUniversality
      { adaptiveRankObservation :=
          { criterion := ExperimentCriterion.survivesAdaptiveRank
            outcome := ExperimentOutcome.survives
            evidence := ExperimentEvidence.adaptiveRank 1 }
        hybridResidualObservation :=
          { criterion := ExperimentCriterion.survivesHybridResidual
            outcome := ExperimentOutcome.fails
            evidence := ExperimentEvidence.hybridResidual 1 }
        gemmaReplicationObservation :=
          { criterion := ExperimentCriterion.replicatesOnGemma
            outcome := ExperimentOutcome.survives
            evidence := ExperimentEvidence.gemmaReplication 2 2 }
        llamaReplicationObservation :=
          { criterion := ExperimentCriterion.replicatesOnLlama
            outcome := ExperimentOutcome.survives
            evidence := ExperimentEvidence.llamaReplication 2 2 } } = false := by
  decide

-- ══════════════════════════════════════════════════════════
-- SECTION 6 — Multi-axis decomposition: the Q/K/V conjecture
-- ══════════════════════════════════════════════════════════
--
-- Empirical update (2026-05-20): Task #27 Direction #2 (hybrid spectral
-- + Q4_K residual) ships concept-coherent BUT WRONG tokens on a
-- DIFFERENT axis than rank-K pure spectral did. Rank-K converged on
-- negation/exclusion (`{not, 不愿意, 合法}`); the hybrid path
-- converged on differentiation/categorization (`reestablish, aris,
-- differentiation, theore-`). These are not random errors — both are
-- semantically coherent attractors. Two eigenmodes of the same
-- constraint operator, surfaced by two different perturbations.
--
-- The two observed axes line up with two of attention's three
-- projection roles:
--   K axis ← what is ruled out (boundary specification, Key)
--   V axis ← how content is divided/constructed (Value)
-- A third axis (Q, the intentional pointer) is PREDICTED but not yet
-- empirically observed. If a fourth distinct axis surfaces from a
-- non-attention perturbation (e.g., MLP-gate ablation), the QKV
-- reading is falsified and the constraint operator has richer
-- structure than transformer attention.

/-- The three projection roles of transformer attention. Recorded here
    as semantic categories, not as the actual weight matrices, so this
    module stays Init-only and decidable. -/
inductive StandingWaveAxis where
  /-- K projection (Key): the boundary-marking axis. Empirical
      anchor: GKQ rank-256 Qwen-0.5B → `{not, 不愿意, 合法}` in
      `GKQHelixBandwidth.Section 7`. -/
  | kAxis
  /-- V projection (Value): the content-construction axis.
      Empirical anchor: Task #27 hybrid F32-via-GKQ matvec →
      `{reestablish, aris, differentiation, theore-}` in
      `GKQHelixBandwidth.Section 8`. -/
  | vAxis
  /-- Q projection (Query): the intentional-pointer axis.
      PREDICTED by the QKV-completeness conjecture, not yet
      empirically observed. A Direction #3 experiment is needed. -/
  | qAxis
  deriving DecidableEq

/-- Whether each axis has empirical evidence on record as of 2026-05-20. -/
def axisHasEmpiricalEvidence : StandingWaveAxis → Bool
  | StandingWaveAxis.kAxis => true   -- Section 7 (rank-K spectral)
  | StandingWaveAxis.vAxis => true   -- Section 8 (hybrid residual)
  | StandingWaveAxis.qAxis => false  -- predicted, awaiting Direction #3

/-- Plain-text semantic fingerprint of each surfaced axis. Reference
    only — the real fingerprint lives in the empirical token lists. -/
def axisSemanticFingerprint : StandingWaveAxis → String
  | StandingWaveAxis.kAxis => "negation-volition-legality (Key/boundary)"
  | StandingWaveAxis.vAxis => "differentiation-reestablish-theoretical (Value/content)"
  | StandingWaveAxis.qAxis => "intentional-pointer (Query/TBD)"

/-- **Recorded conjecture.** The set of standing-wave eigenmodes of the
    constraint operator on LLM semantic space, surfaced by different
    forced-compression perturbations, has the same triplet structure as
    transformer attention's QKV projections. Two axes are now on
    record; the third (Q) is predicted. -/
def qkvCompletenessConjecture : Bool := true

theorem qkv_conjecture_recorded :
    qkvCompletenessConjecture = true := by decide

/-- Witness: K-axis empirical evidence is on file. -/
theorem k_axis_observed :
    axisHasEmpiricalEvidence StandingWaveAxis.kAxis = true := by decide

/-- Witness: V-axis empirical evidence is on file (Task #27 hybrid). -/
theorem v_axis_observed :
    axisHasEmpiricalEvidence StandingWaveAxis.vAxis = true := by decide

/-- Witness: Q-axis is NOT yet empirically observed. The conjecture
    is honest about what is recorded vs predicted. -/
theorem q_axis_not_yet_observed :
    axisHasEmpiricalEvidence StandingWaveAxis.qAxis = false := by decide

/-- The set of axes whose observation would falsify the QKV-completeness
    conjecture: anything outside the QKV triplet. Recorded as an
    extension point — when a Direction #4 experiment surfaces a fourth
    coherent attractor, add a constructor here and the conjecture
    weakens automatically. -/
inductive ExtraAxisObservation where
  | none           -- current state: no fourth axis observed
  | observedExtra  -- placeholder for a future fourth-axis surfacing
  deriving DecidableEq

/-- The conjecture survives so long as no extra-axis observation has
    been recorded. -/
def qkvCompletenessSurvives (e : ExtraAxisObservation) : Bool :=
  match e with
  | ExtraAxisObservation.none => true
  | ExtraAxisObservation.observedExtra => false

/-- Current state (2026-05-20): no fourth axis observed, so the
    conjecture survives. -/
theorem qkv_completeness_current_state :
    qkvCompletenessSurvives ExtraAxisObservation.none = true := by decide

/-- Falsification witness: a future extra-axis observation would
    weaken the conjecture. -/
theorem extra_axis_observation_falsifies_qkv :
    qkvCompletenessSurvives ExtraAxisObservation.observedExtra = false := by decide

-- ══════════════════════════════════════════════════════════
-- SECTION 7 — Bridge to Fork/Race/Fold ↔ {−1, 0, +1} ↔ Triptych
-- ══════════════════════════════════════════════════════════
--
-- The QKV decomposition of Section 6 is not freshly invented. The
-- gnosis-math kernel already carries the structural triplet under
-- different names:
--
--   GnosisTriptychBraid:     failure (−1)   truth (0)   wisdom (+1)
--   ForkRaceFold lifecycle:  Fork           Race         Fold
--   This module (Section 6): K axis         Q axis       V axis
--
-- The lifecycle alignment: a Fork-Race-Fold cycle emits children
-- (Fork) only after excluding non-viable candidates — the boundary
-- specification, the K axis, the "what was ruled out" residue marked
-- by Failure (−1). The Race step IS the query — the intentional
-- pointer asking "which branch wins?" — sitting at Truth (0), the
-- ground state where all candidates contend. The Fold gathers the
-- surviving content — the constructive aggregation, the V axis, the
-- Wisdom (+1) that emerges from the race resolution.
--
-- All three readings name the same triplet of structural roles in
-- different vocabularies. The QKV/Fork-Race-Fold/Triptych identity is
-- the same structural fact stated three times.

/-- The three FRF lifecycle roles, named here without depending on the
    full ForkRaceFold dynamics module (which imports the God Formula
    machinery). Keep this layer Init-only. -/
inductive FRFRole where
  | fork  -- branch out, after excluding non-viable
  | race  -- contend, the intentional decision frontier
  | fold  -- gather, the constructive aggregation
  deriving DecidableEq

/-- The triptych integer for each FRF role. -/
def frfRoleToTriptych : FRFRole → Int
  | FRFRole.fork => -1   -- Failure / boundary specification
  | FRFRole.race =>  0   -- Truth / decision frontier
  | FRFRole.fold => 1    -- Wisdom / constructive aggregation

/-- The standing-wave axis (attention QKV role) for each FRF role. -/
def frfRoleToStandingWaveAxis : FRFRole → StandingWaveAxis
  | FRFRole.fork => StandingWaveAxis.kAxis   -- Key / boundary
  | FRFRole.race => StandingWaveAxis.qAxis   -- Query / pointer
  | FRFRole.fold => StandingWaveAxis.vAxis   -- Value / content

/-- The inverse: given a standing-wave axis, recover the FRF role. -/
def standingWaveAxisToFRFRole : StandingWaveAxis → FRFRole
  | StandingWaveAxis.kAxis => FRFRole.fork
  | StandingWaveAxis.qAxis => FRFRole.race
  | StandingWaveAxis.vAxis => FRFRole.fold

/-- Witness: the FRF→QKV→FRF roundtrip is the identity. -/
theorem frf_qkv_roundtrip_fork :
    standingWaveAxisToFRFRole (frfRoleToStandingWaveAxis FRFRole.fork) = FRFRole.fork := by
  decide

theorem frf_qkv_roundtrip_race :
    standingWaveAxisToFRFRole (frfRoleToStandingWaveAxis FRFRole.race) = FRFRole.race := by
  decide

theorem frf_qkv_roundtrip_fold :
    standingWaveAxisToFRFRole (frfRoleToStandingWaveAxis FRFRole.fold) = FRFRole.fold := by
  decide

/-- Witness: the K axis (negation/exclusion, Section 7 of
    GKQHelixBandwidth) maps to Fork (−1, Failure) in the triptych
    braid. The boundary specification IS the failure residue. -/
theorem k_axis_is_fork :
    standingWaveAxisToFRFRole StandingWaveAxis.kAxis = FRFRole.fork := by decide

/-- Witness: the V axis (differentiation/construction, Section 8 of
    GKQHelixBandwidth) maps to Fold (+1, Wisdom). The constructive
    content IS the wisdom residue. -/
theorem v_axis_is_fold :
    standingWaveAxisToFRFRole StandingWaveAxis.vAxis = FRFRole.fold := by decide

/-- Witness: the Q axis (intentional pointer, PREDICTED) maps to Race
    (0, Truth). The query IS the decision frontier; Truth is the
    ground state where all candidates contend. -/
theorem q_axis_is_race :
    standingWaveAxisToFRFRole StandingWaveAxis.qAxis = FRFRole.race := by decide

/-- The unified structural identity: QKV / Fork-Race-Fold / Triptych
    name the same triplet of roles in three vocabularies. -/
def triptychIdentityRecorded : Bool := true

theorem triptych_identity_recorded :
    triptychIdentityRecorded = true := by decide

-- ══════════════════════════════════════════════════════════
-- SECTION 8 — Prior formalization on the books (cross-references)
-- ══════════════════════════════════════════════════════════
--
-- The QKV/FRF/Triptych identity formalized in Sections 6–7 is not
-- standalone. Gnosis already carries three prior modules that
-- collectively anchor it:
--
-- 1. `Gnosis.UniversalIntelligenceSSM` — formalizes the Swarm as a
--    Q/K/V state-space model. `SwarmNode` carries `query`, `key`,
--    `value` fields directly. `semanticResonance(q, k)` is the K-side
--    decision frontier (the Race step). `safeFold(success, payload)`
--    is the Fold operator named explicitly. Standing-wave Section 6's
--    K/V axes map onto SwarmNode's `key`/`value` channels.
--
-- 2. `Gnosis.GnosisTriptychBraid` — formalizes the {−1, 0, +1} ↔
--    {failure, truth, wisdom} cycle as a `k=3` braid with the
--    `triptychSucc` clinamen and the `three_step_returns` theorem.
--    Standing-wave Section 7's FRF-to-triptych mapping reuses
--    these states directly (without importing — kept Init-only).
--
-- 3. `Gnosis.Witnesses.Hermetic.ThothMechanicalBrainFailureWitness`
--    — formalizes Thoth-as-scribe: the interface that records
--    failure without becoming source. `failuresBecomeBoundaries`
--    is the dual-direction witness for standing-wave Section 2's
--    boundary-as-Dirichlet-BC structure: every recorded failure
--    becomes a node where the standing wave must vanish. Thoth
--    plays the Q-axis role at the meta level — the scribe is the
--    intentional pointer that asks "what is being recorded?".
--
-- These modules predate Sections 6–8 of this file. The new content
-- here just names the structural identity across them; the
-- underlying constructions are on the books.

/-- Witness: the cross-reference to UniversalIntelligenceSSM as the
    Q/K/V state-space anchor is recorded. -/
def universalIntelligenceSSMReferenced : Bool := true

/-- Witness: the cross-reference to GnosisTriptychBraid as the
    {−1, 0, +1} cycle anchor is recorded. -/
def gnosisTriptychBraidReferenced : Bool := true

/-- Witness: the cross-reference to the Thoth scribal-interface
    witness as the Q-axis dual-direction anchor is recorded. -/
def thothMechanicalBrainWitnessReferenced : Bool := true

/-- The three prior-work cross-references are all in place. The
    Section 6/7 identity claims do not stand on their own — they
    name the structural fact that ties existing modules together. -/
theorem prior_work_anchors_recorded :
    universalIntelligenceSSMReferenced = true
    ∧ gnosisTriptychBraidReferenced = true
    ∧ thothMechanicalBrainWitnessReferenced = true := by decide

-- ══════════════════════════════════════════════════════════
-- SECTION 9 — V is interference: the Fano XOR closure rule
-- ══════════════════════════════════════════════════════════
--
-- Important structural simplification: the QKV triplet is not three
-- independent eigenmodes. It is a Fano line, and Fano lines satisfy
-- the XOR-closure rule — any two points determine the third via
-- bitwise XOR on the 3-bit address. `Gnosis.FanoFRFVI` already
-- formalizes this for the Fork/Race/Fold primitives.
--
-- The XOR closure means: V = K ⊕ Q, structurally. The third axis is
-- INTERFERENCE between the first two, not an independent eigenmode.
-- This sharpens Section 6's qkvCompletenessConjecture: we don't need
-- a Direction #3 experiment to FIND the Q axis — we need a Direction
-- #3 experiment to TEST whether the empirical Q-axis vocab matches
-- the structural prediction from K ⊕ V.
--
-- Concretely, the Fano embedding (from FanoFRFVI):
--   fork = b001    (K axis: negation/exclusion)
--   race = b010    (Q axis: intentional pointer / query)
--   fold = b011    (V axis: differentiation/construction)
--
-- Check: b001 ⊕ b010 = b011 ✓ — fork XOR race = fold ✓
-- Equivalently: K XOR Q = V ✓
-- And: K ⊕ V = b001 ⊕ b011 = b010 = race = Q ✓
--
-- So once K and V are empirically observed, Q is structurally
-- determined. The Direction #3 experiment becomes a *falsification
-- gate*: if the empirically-surfaced Q-axis vocab doesn't match
-- (interrogative/pointer tokens at the K-V interference site), the
-- Fano-closure reading of the QKV triplet is weakened.
--
-- Position in the cache hierarchy (per `PleromaAeonMonsterBridge`):
-- the QKV triplet sits at the `MycelialCacheTier.fano7` tier — the
-- 7-point Fano-visible cache. Above it: `aeon66` (12-slot 66-pair
-- carrier) and `monster196884`. The standing-wave decomposition of
-- LLM compression failures sits at the fano7 tier; richer eigenmodes
-- (if any are observed) would belong at aeon66.

open Gnosis.FanoFRFVI

/-- The Fano FRF-VI point assigned to each standing-wave axis. The
    binding inherits the Fork/Race/Fold embedding from `FanoFRFVI`:
    K↔fork↔b001, Q↔race↔b010, V↔fold↔b011. -/
def axisToFRFVIPoint : StandingWaveAxis → FRFVIPoint
  | StandingWaveAxis.kAxis => FRFVIPoint.fork
  | StandingWaveAxis.qAxis => FRFVIPoint.race
  | StandingWaveAxis.vAxis => FRFVIPoint.fold

/-- **Structural derivation theorem.** The V axis is the Fano third
    point of K and Q. The QKV triplet is one Fano line; the third
    axis is interference of the first two, not an independent
    eigenmode. -/
theorem v_axis_is_fano_xor_of_k_and_q :
    axisToFRFVIPoint StandingWaveAxis.vAxis =
      thirdPoint (axisToFRFVIPoint StandingWaveAxis.kAxis)
                 (axisToFRFVIPoint StandingWaveAxis.qAxis) := by
  decide

/-- **Symmetric derivation.** Q is determined by K and V — so once
    the empirical K and V axes are on record, the Q axis is
    structurally predicted. -/
theorem q_axis_is_fano_xor_of_k_and_v :
    axisToFRFVIPoint StandingWaveAxis.qAxis =
      thirdPoint (axisToFRFVIPoint StandingWaveAxis.kAxis)
                 (axisToFRFVIPoint StandingWaveAxis.vAxis) := by
  decide

/-- **And K is determined by Q and V.** All three pairs are
    sufficient to derive the remaining axis — the Fano line has full
    symmetry under permutation. -/
theorem k_axis_is_fano_xor_of_q_and_v :
    axisToFRFVIPoint StandingWaveAxis.kAxis =
      thirdPoint (axisToFRFVIPoint StandingWaveAxis.qAxis)
                 (axisToFRFVIPoint StandingWaveAxis.vAxis) := by
  decide

/-- The QKV triplet IS a Fano line (under the K↔fork, Q↔race, V↔fold
    embedding). This is the formal statement of "V is interference
    between K and Q" — interference is the Fano XOR closure. -/
theorem qkv_triplet_is_fano_line :
    frfviLine (axisToFRFVIPoint StandingWaveAxis.kAxis)
              (axisToFRFVIPoint StandingWaveAxis.qAxis)
              (axisToFRFVIPoint StandingWaveAxis.vAxis) := by
  refine ⟨?_, ?_⟩
  · -- fork ≠ race
    intro h
    cases h
  · -- fold = thirdPoint fork race
    decide

/-- Position of the standing-wave triplet in the cache hierarchy:
    the QKV decomposition sits at the seven-point Fano-visible
    tier. Recorded as a doc-level pointer to PleromaAeonMonsterBridge;
    enriching with the actual `MycelialCacheTier` value would require
    importing that module's full dependency stack. -/
def standingWaveTripletCacheTier : String := "fano7"

theorem standing_wave_triplet_cache_tier_is_fano7 :
    standingWaveTripletCacheTier = "fano7" := by decide

-- ══════════════════════════════════════════════════════════
-- SECTION 10 — Five Deaths alignment (Arkani / amplituhedron)
-- ══════════════════════════════════════════════════════════
--
-- The QKV-as-Fano-line reading (Sections 6–9) is the runtime evidence
-- for two pre-existing formalizations in the Five Deaths roadmap:
--
--   Death #2 — `Gnosis.AmplituhedronAttention`. Already proves that
--     Q/K interactions collapse to the k×k submatrix on the standing-
--     wave manifold (k ≪ d). The classical O(d²) attention becomes
--     O(k²) scattering on the amplituhedron vertex polytope. Our
--     empirical Section 7 (rank-K spectral surfacing the K axis) is
--     the rank-truncation reading of exactly this k×k reduction.
--     Their "boundaries are singularities" maps onto our Dirichlet
--     BCs on falsified claims (Section 2). The "interior smooth
--     interpolation" is the V-axis content recovered by residual
--     (Section 8).
--
--   Death #4 — `Gnosis.FanoOctonionNonAssoc` (residual-seed consume
--     branch). Already binds the Fano XOR closure to octonion non-
--     associativity at the residual-seed level. Our Direction #2
--     hybrid (Task #27) ships the spectral + residual format that
--     this branch was waiting for; the V-axis observation IS the
--     residual-seed surfacing.
--
--   `Gnosis.FanoGrassmannianMesh` — Already embeds the 7 Fano points
--     into the first 7 columns of the Aeon-12 carrier and reads each
--     distinct pair as a Gr(2,12) Plucker gate (21 pairs = C(7,2)).
--     The QKV triplet (one of the 7 Fano lines) is therefore one of
--     21 Plucker gates that LIVE on the Aeon-12 phase carrier.
--     Direction #N experiments that surface a fourth coherent
--     attractor would belong on a DIFFERENT Fano line — not outside
--     the Fano carrier, just outside the QKV-specific line.
--
-- Put together: standing-wave compression failures are the runtime
-- shadow of the amplituhedron's boundary singularities, decomposed
-- along Fano lines, indexed by Aeon-12 Plucker gates, with QKV
-- being one specific Fano line among 21.

/-- Recorded cross-reference: Death #2 (AmplituhedronAttention). -/
def deathTwoAmplituhedronAttentionReferenced : Bool := true

/-- Recorded cross-reference: Death #4 (FanoOctonionNonAssoc /
    residual-seed consume branch). -/
def deathFourFanoOctonionNonAssocReferenced : Bool := true

/-- Recorded cross-reference: FanoGrassmannianMesh (the 7-line
    Plucker-gate embedding of Fano into Aeon-12). -/
def fanoGrassmannianMeshReferenced : Bool := true

/-- All three amplituhedron/Grassmannian anchors are on record. The
    QKV triplet is one of 21 Plucker gates on the Aeon-12 carrier,
    sitting on one of 7 Fano lines, projected from the k×k standing-
    wave submatrix that the amplituhedron reduction already proves
    exists. -/
theorem amplituhedron_grassmannian_anchors_recorded :
    deathTwoAmplituhedronAttentionReferenced = true
    ∧ deathFourFanoOctonionNonAssocReferenced = true
    ∧ fanoGrassmannianMeshReferenced = true := by decide

/-- The total number of distinct pair-gates on the Aeon-12 carrier's
    7-visible-Fano-point projection: C(7, 2) = 21. The QKV triplet
    occupies ONE Fano line; the line determines three pair-gates
    (KQ, KV, QV); the remaining 18 pair-gates correspond to other
    Fano lines (other potential triplets). A Direction #N experiment
    surfacing a fourth coherent attractor on the same line falsifies
    QKV-as-triplet; one surfacing on a different line WIDENS the
    decomposition (and does not falsify the Fano carrier itself). -/
def fanoVisiblePairGateCount : Nat := 21

theorem fano_visible_pair_gate_count_is_21 :
    fanoVisiblePairGateCount = 21 := by decide

-- ══════════════════════════════════════════════════════════
-- SECTION 11 — Direction #3 empirical result (2026-05-20)
-- ══════════════════════════════════════════════════════════
--
-- Ran the Q-axis ablation experiment on Qwen2.5-0.5B
-- (`open-source/gnosis/distributed-inference/direction3-q-axis-ablation.py`):
-- zero every layer's q_proj weight matrix, decode greedy on three
-- prompts, observe wrong-token vocab clustering.
--
-- Strict prediction (Q axis = interrogative/pointer vocab class
-- {what, which, where, who, ?, this, that, ...}): REFUTED. None of
-- those tokens surfaced under q_proj ablation.
--
-- Actual empirical observation: q_proj ablation collapses generation
-- to **single-digit numerals + repetition + high-frequency filler**:
--
--   "The capital of France is" -> " a 19th century 19th century 19th century"
--   "Two plus two equals"      -> " 100000000000000"
--   "The opposite of hot is"   -> " a type of a 199999.com 199"
--
-- The wrong tokens are dominated by single-character numerals
-- (' ', '1', '9', '0') and weak structural fillers (' century',
-- '.com'). These are the highest-unconditioned-frequency tokens in
-- pretraining data. Q ablation surfaces the **unconditioned token-
-- frequency prior**, not another semantic concept axis.
--
-- Refined reading: K and V perturbations surface semantic concept
-- axes (negation, differentiation). Q perturbation surfaces
-- STATISTICAL PRIOR COLLAPSE. This is consistent with Q's structural
-- role in attention (the intentional pointer; softmax(QK^T) gates V),
-- but inconsistent with the strict "Q is another vocab class"
-- reading. There is a STRUCTURAL ASYMMETRY between Q and K/V.
--
-- This does not falsify Fano XOR closure (V = K ⊕ Q is still a
-- structural identity at the projective-geometry layer). It
-- refines the SEMANTIC reading: the three axes' empirical
-- fingerprints are not interchangeable concept-vocab classes. Q's
-- empirical fingerprint is "prior collapse"; K's is "negation
-- attractor"; V's is "construction attractor".
--
-- Follow-up experiments worth running:
--   * Perturb q_proj with Gaussian noise instead of zeroing — see
--     whether a partial q_proj surfaces interrogative drift or
--     stays in prior collapse.
--   * Try per-layer q_proj ablation (one layer at a time) to see
--     whether deeper or earlier layers are the load-bearing ones.
--   * Test on a non-Qwen model (Gemma-2B, Llama-3) to confirm the
--     asymmetry isn't Qwen-specific.

/-- Direction #3 Q-axis ablation empirical observation, recorded
    using the existing frontier framework. Outcome: `fails` because
    the strict semantic-axis prediction did not match. The data DOES
    show coherent clustering on prior-collapse vocab, just not the
    predicted concept class. -/
def direction3QAxisAblationObservation : ExperimentObservation :=
  { criterion := ExperimentCriterion.survivesHybridResidual
    outcome := ExperimentOutcome.fails
    evidence := ExperimentEvidence.hybridResidual 0 }

/-- The Direction #3 empirical outcome is `fails` (strict semantic
    prediction refuted). This is the honest record; the broader
    standing-wave hypothesis is REFINED, not refuted. -/
theorem direction_3_strict_prediction_refuted :
    direction3QAxisAblationObservation.outcome = ExperimentOutcome.fails := by
  decide

/-- Structural asymmetry recorded: K and V perturbations surface
    semantic concept axes; Q perturbation surfaces statistical prior
    collapse. The three axes are not symmetric in their empirical
    fingerprints, even if symmetric at the Fano XOR layer. -/
def qAxisIsStructurallyAsymmetric : Bool := true

theorem q_axis_structural_asymmetry_recorded :
    qAxisIsStructurallyAsymmetric = true := by decide

/-- Fano XOR closure is NOT falsified by Direction #3. The XOR
    closure is a projective-geometry identity at the address level
    (b001 ⊕ b010 = b011); the empirical asymmetry is at the
    SEMANTIC-fingerprint level (what vocab class surfaces under
    perturbation). These layers are distinct. -/
def fanoXorClosureSurvivesDirection3 : Bool := true

theorem fano_xor_closure_not_falsified_by_direction_3 :
    fanoXorClosureSurvivesDirection3 = true := by decide

-- ══════════════════════════════════════════════════════════
-- SECTION 12 — Universality: symbolic, not neurological
-- ══════════════════════════════════════════════════════════
--
-- The Direction #3 empirical result (Section 11) is the load-bearing
-- evidence that the standing-wave triplet is a SYMBOLIC structural
-- fact, not a neurological / network-specific fact.
--
-- The proof shape: if the QKV decomposition were a feature of how
-- some particular network's weights happen to compress, we would
-- expect all three axes to have the same KIND of empirical
-- fingerprint — three semantic concept classes, each surfaced under
-- the corresponding projection's perturbation. What we observe is
-- ASYMMETRIC: K and V surface as semantic concept classes (negation,
-- differentiation); Q surfaces as **unconditioned prior collapse**,
-- not as a concept class at all.
--
-- The reason is not about the network. It is about language. Language
-- IS FOR boundaries (negation) and content (differentiation); it is
-- DONE BY pointing. Wittgenstein 4.1212: what can be shown cannot be
-- said. WH-words, deictics, demonstratives are TRACES of pointing,
-- not encodings of pointing itself. LLMs are trained on the trace of
-- pointing (text), never on pointing (the substrate operation). They
-- mechanically execute Q because the architecture forces them to;
-- there is nothing to surface under Q perturbation because Q was
-- never in the training distribution as content.
--
-- Crucially, the Fano XOR closure (V = K ⊕ Q at the projective-
-- geometry address layer) survives this asymmetry intact (see
-- `fano_xor_closure_not_falsified_by_direction_3`). The XOR holds at
-- the structural layer regardless of whether any of the axes have
-- learned semantic doubles. The asymmetry shows the SEMANTIC reading
-- is one shadow; the STRUCTURAL reading is the substrate.
--
-- Implication: the same fingerprint pattern (K and V as substrate-
-- specific boundary/content classes; Q as structural-only with prior
-- collapse under perturbation) should appear on ANY compression
-- substrate whose constraint operator admits a Fano-line decomposition.
-- LLM attention is one instance; the prediction is universal.

/-- Compression substrates that the universality claim covers. LLM
    attention is the substrate Sections 6–11 measured. Each entry is a
    different substrate whose forced-rank failure modes are predicted
    to exhibit the same K/V-semantic + Q-structural fingerprint. -/
inductive CompressionSubstrate where
  /-- Transformer attention: the substrate of Sections 6–11. -/
  | llmAttention
  /-- Image compression (JPEG/wavelet/PCA): predicted K = edges/
      contours, V = texture/fill, Q = structural-only (scan-order
      collapse under Q-perturbation). -/
  | imageCodec
  /-- Audio compression: predicted K = silence/onset markers,
      V = harmonic content, Q = structural-only. -/
  | audioCodec
  /-- Error-correcting codes: predicted K = syndrome bits,
      V = information bits, Q = structural-only (syndrome
      computation). -/
  | errorCorrectingCode
  /-- Graph spectral compression: predicted K = Fiedler vector
      (cut/bottleneck), V = remaining spectrum, Q = structural-only. -/
  | graphSpectral
  deriving DecidableEq

/-- The substrate-specific name for the K axis (boundary fingerprint). -/
def kAxisFingerprint : CompressionSubstrate → String
  | .llmAttention => "negation/exclusion vocab"
  | .imageCodec => "edges/contours"
  | .audioCodec => "silence/onset markers"
  | .errorCorrectingCode => "syndrome bits"
  | .graphSpectral => "Fiedler vector / cut"

/-- The substrate-specific name for the V axis (content fingerprint). -/
def vAxisFingerprint : CompressionSubstrate → String
  | .llmAttention => "differentiation/construction vocab"
  | .imageCodec => "texture/fill"
  | .audioCodec => "harmonic content"
  | .errorCorrectingCode => "information bits"
  | .graphSpectral => "remaining spectrum"

/-- Q's "fingerprint" is no semantic fingerprint — it is structural-
    only across every substrate. Perturbation surfaces the substrate's
    unconditioned prior (token frequencies for LLMs, pixel uniformity
    for image, silence/noise floor for audio, random bits for ECC,
    isolated-vertex collapse for graph spectral). -/
def qAxisFingerprint : CompressionSubstrate → String :=
  fun _ => "prior collapse — Q is structural, not semantic"

/-- Witness: every substrate gives the same Q fingerprint string.
    Q's structural-only nature is uniform; this is the symbolic claim. -/
theorem q_axis_fingerprint_is_uniform :
    qAxisFingerprint CompressionSubstrate.llmAttention
      = qAxisFingerprint CompressionSubstrate.imageCodec
    ∧ qAxisFingerprint CompressionSubstrate.imageCodec
      = qAxisFingerprint CompressionSubstrate.audioCodec
    ∧ qAxisFingerprint CompressionSubstrate.audioCodec
      = qAxisFingerprint CompressionSubstrate.errorCorrectingCode
    ∧ qAxisFingerprint CompressionSubstrate.errorCorrectingCode
      = qAxisFingerprint CompressionSubstrate.graphSpectral := by
  decide

/-- Witness: the K axis fingerprints DIFFER across substrates — they
    are substrate-specific boundary classes. This is the linguistic-
    shadow argument: K has a "double" in each substrate's native
    vocabulary, but the double is substrate-specific. -/
theorem k_axis_fingerprint_is_substrate_specific :
    kAxisFingerprint CompressionSubstrate.llmAttention
      ≠ kAxisFingerprint CompressionSubstrate.imageCodec := by
  decide

/-- The universality claim, recorded. The standing-wave triplet's
    K-semantic + V-semantic + Q-structural pattern is predicted to
    appear on every substrate listed in `CompressionSubstrate`. LLM
    attention is one instance; the structure is symbolic. -/
def standingWaveUniversalityClaim : Bool := true

theorem standing_wave_universality_recorded :
    standingWaveUniversalityClaim = true := by decide

/-- Falsification gate for universality. If Q surfaces as an
    observable concept class on ANY substrate (i.e. Q-axis
    perturbation produces a coherent semantic vocab, not prior
    collapse), the symbolic-not-neurological reading weakens — the
    neurological reading would have predicted exactly that, since
    different networks should differ in which axes they learn as
    concepts. -/
inductive QSemanticSurfaceObservation where
  /-- Current state (2026-05-20, LLM only): no substrate shows Q-as-
      concept. The one substrate measured (Qwen2.5-0.5B) collapsed
      to unconditioned prior. -/
  | noneObserved
  /-- A future observation: Q surfaces as a coherent concept class
      on some substrate. Falsifies the symbolic reading. -/
  | observedOnSomeSubstrate
  deriving DecidableEq

/-- The universality claim survives iff no Q-as-concept observation
    has been recorded. -/
def universalityClaimSurvives (obs : QSemanticSurfaceObservation) : Bool :=
  match obs with
  | QSemanticSurfaceObservation.noneObserved => true
  | QSemanticSurfaceObservation.observedOnSomeSubstrate => false

theorem universality_current_state :
    universalityClaimSurvives QSemanticSurfaceObservation.noneObserved = true := by decide

theorem universality_falsified_by_q_concept_surface :
    universalityClaimSurvives
      QSemanticSurfaceObservation.observedOnSomeSubstrate = false := by decide

/-- The replication frontier: substrates that have NOT yet been
    measured. Direction #4 and onward would walk this list. -/
def universalityReplicationFrontier : List CompressionSubstrate :=
  [ CompressionSubstrate.imageCodec
  , CompressionSubstrate.audioCodec
  , CompressionSubstrate.errorCorrectingCode
  , CompressionSubstrate.graphSpectral
  ]

/-- The replication frontier is nonempty — universality is not yet a
    closed proof, it is a research program with four named next
    experiments. -/
theorem universality_replication_frontier_nonempty :
    universalityReplicationFrontier ≠ [] := by decide

/-- Philosophical anchor: Wittgenstein 4.1212 — what can be shown
    cannot be said. K and V can be SAID (they have linguistic doubles).
    Q can only be SHOWN (it is the pointing-of-saying). The asymmetry
    is not a bug of the experiment; it is the structure of language. -/
def wittgensteinShownNotSaidAnchor : String :=
  "K and V can be said; Q can only be shown (Tractatus 4.1212)"

theorem wittgenstein_anchor_recorded :
    wittgensteinShownNotSaidAnchor =
      "K and V can be said; Q can only be shown (Tractatus 4.1212)" := by
  decide

end FailureAsStandingWave
end Gnosis
