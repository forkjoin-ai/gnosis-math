import Init

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

end FailureAsStandingWave
end Gnosis
