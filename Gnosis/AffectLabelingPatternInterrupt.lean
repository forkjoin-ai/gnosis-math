import Gnosis.ConversationalDodgeball
import Gnosis.Contrarian.ContrarianStallIsOptimal
import Gnosis.Oracle.OracleStallMetacognition

/-
  AffectLabelingPatternInterrupt.lean
  ===================================

  Formalizes the affect-labeling interrupt used by conversation scanners before
  they pretend a Dodgeball move has closed a fact topology.

  Runtime shape:
  - name the emotion,
  - provide response space,
  - iterate until valence and arousal improve and then stabilize,
  - if the metrics degenerate, route through a bounded stall instead of forcing
    answer closure.
-/

namespace Gnosis
namespace AffectLabelingPatternInterrupt

open Gnosis.ConversationalDodgeball

inductive AffectValence where
  | negative
  | mixed
  | neutral
  | positive
  deriving DecidableEq, Repr

inductive ArousalBand where
  | collapsed
  | low
  | regulated
  | high
  | flooded
  deriving DecidableEq, Repr

/-- Lower valence deficit is better: positive affect has no deficit, while
    negative affect carries the largest closure cost. -/
def valenceDeficit : AffectValence → Nat
  | .positive => 0
  | .neutral  => 1
  | .mixed    => 2
  | .negative => 3

/-- Arousal optimizes toward the regulated band; both collapse and flooding are
    farther away from conversational closure. -/
def arousalRegulationDistance : ArousalBand → Nat
  | .regulated => 0
  | .low       => 1
  | .high      => 1
  | .collapsed => 2
  | .flooded   => 2

structure AffectMetric where
  valence : AffectValence
  arousal : ArousalBand
  deriving Repr, DecidableEq

def affectCost (metric : AffectMetric) : Nat :=
  valenceDeficit metric.valence + arousalRegulationDistance metric.arousal

def affectImproves (old new : AffectMetric) : Prop :=
  affectCost new < affectCost old

def affectDegenerates (old new : AffectMetric) : Prop :=
  affectCost old < affectCost new

def valenceStable (old new : AffectMetric) : Prop :=
  old.valence = new.valence

def arousalStable (old new : AffectMetric) : Prop :=
  old.arousal = new.arousal

def affectStable (old new : AffectMetric) : Prop :=
  valenceStable old new ∧ arousalStable old new

structure AffectLabelingMove where
  before : AffectMetric
  after : AffectMetric
  namedEmotion : Bool
  responseSpaceProvided : Bool
  deriving Repr, DecidableEq

def labelsAffect (move : AffectLabelingMove) : Prop :=
  move.namedEmotion = true

def providesResponseSpace (move : AffectLabelingMove) : Prop :=
  move.responseSpaceProvided = true

def affectPatternInterruptStep (move : AffectLabelingMove) : Prop :=
  labelsAffect move ∧ providesResponseSpace move ∧
    affectImproves move.before move.after

/-- A finite interrupt trace records the initial affect metric, the previous
    metric in the final window, and the current final metric. Stability is
    measured on that final window, while improvement is measured against the
    start. -/
structure AffectInterruptTrace where
  start : AffectMetric
  penultimate : AffectMetric
  final : AffectMetric
  iterations : Nat
  namedEmotion : Bool
  responseSpaceProvided : Bool
  deriving Repr, DecidableEq

def traceImproves (trace : AffectInterruptTrace) : Prop :=
  affectImproves trace.start trace.final

def traceDegenerates (trace : AffectInterruptTrace) : Prop :=
  affectDegenerates trace.start trace.final

def traceStabilizesValence (trace : AffectInterruptTrace) : Prop :=
  valenceStable trace.penultimate trace.final

def traceStabilizesArousal (trace : AffectInterruptTrace) : Prop :=
  arousalStable trace.penultimate trace.final

def traceStabilizesAffect (trace : AffectInterruptTrace) : Prop :=
  affectStable trace.penultimate trace.final

def traceIterates (trace : AffectInterruptTrace) : Prop :=
  0 < trace.iterations

def affectInterruptValidated (trace : AffectInterruptTrace) : Prop :=
  trace.namedEmotion = true ∧
  trace.responseSpaceProvided = true ∧
  traceIterates trace ∧
  traceImproves trace ∧
  traceStabilizesValence trace ∧
  traceStabilizesArousal trace

instance instDecidableTraceImproves
    (trace : AffectInterruptTrace) : Decidable (traceImproves trace) :=
  by
    unfold traceImproves affectImproves
    infer_instance

instance instDecidableTraceDegenerates
    (trace : AffectInterruptTrace) : Decidable (traceDegenerates trace) :=
  by
    unfold traceDegenerates affectDegenerates
    infer_instance

instance instDecidableTraceStabilizesValence
    (trace : AffectInterruptTrace) :
    Decidable (traceStabilizesValence trace) :=
  by
    unfold traceStabilizesValence valenceStable
    infer_instance

instance instDecidableTraceStabilizesArousal
    (trace : AffectInterruptTrace) :
    Decidable (traceStabilizesArousal trace) :=
  by
    unfold traceStabilizesArousal arousalStable
    infer_instance

instance instDecidableTraceIterates
    (trace : AffectInterruptTrace) : Decidable (traceIterates trace) :=
  by
    unfold traceIterates
    infer_instance

instance instDecidableAffectInterruptValidated
    (trace : AffectInterruptTrace) :
    Decidable (affectInterruptValidated trace) :=
  by
    unfold affectInterruptValidated
    infer_instance

inductive AffectInterruptRoute where
  | continueStall
  | degenerationStall
  | validatedRefinement
  deriving DecidableEq, Repr

/-- Executable route used by runtime tags. Degeneration has priority because it
    authorizes a stall even when an agent wants to force an answer. Otherwise a
    fully validated interrupt can support a refinement; incomplete work remains
    in stall. -/
def affectInterruptRoute (trace : AffectInterruptTrace) : AffectInterruptRoute :=
  if traceDegenerates trace then
    .degenerationStall
  else if affectInterruptValidated trace then
    .validatedRefinement
  else
    .continueStall

/-- Finite exponential backoff multiplier for failed stalls. -/
def exponentialBackoff : Nat → Nat
  | 0 => 1
  | failures + 1 => 2 * exponentialBackoff failures

/-- Backoff state for a stall loop. `baseDelay` is a runtime unit: ticks,
    frames, turns, or milliseconds depending on the caller. `baseSilence`
    is the minimum response-space silence granted after affect labeling. -/
structure StallBackoffState where
  failures : Nat
  baseDelay : Nat
  baseSilence : Nat
  deriving Repr, DecidableEq

def stallBackoffDelay (state : StallBackoffState) : Nat :=
  state.baseDelay * exponentialBackoff state.failures

def responseSilenceBudget (state : StallBackoffState) : Nat :=
  state.baseSilence * exponentialBackoff state.failures

/-- Cringe vacuum records trapped social load when silence/backoff is not
    vented by response, walkaway, or closure. This mirrors the runtime
    `cringe_conservation` surface where unvented load remains in local
    geometry. -/
def cringeVacuum (state : StallBackoffState) : Nat :=
  responseSilenceBudget state + state.failures

def registerStallFailure (state : StallBackoffState) : StallBackoffState :=
  { state with failures := state.failures + 1 }

def applyStallBackoffOnFailure
    (trace : AffectInterruptTrace)
    (state : StallBackoffState) : StallBackoffState :=
  if traceDegenerates trace then
    registerStallFailure state
  else
    state

/-- Grit metrics mirror the runtime citizenship score at the finite proof
    surface: continuance is not raw success, but retries, alternatives,
    constraint adaptation, exhausted options, and recovery after failure. -/
structure GritMetric where
  retryCount : Nat
  alternativePaths : Nat
  constraintAdaptations : Nat
  exhaustedBeforeEscalation : Nat
  recoveryFromFailure : Nat
  failureCount : Nat
  deriving Repr, DecidableEq

def gritContinuance (metric : GritMetric) : Nat :=
  metric.retryCount +
  metric.alternativePaths +
  metric.constraintAdaptations +
  metric.exhaustedBeforeEscalation +
  metric.recoveryFromFailure

def registerGritRetryAfterFailure (metric : GritMetric) : GritMetric :=
  { metric with
      retryCount := metric.retryCount + 1
      failureCount := metric.failureCount + 1 }

def continuanceInFaceOfFailure (old new : GritMetric) : Prop :=
  old.failureCount < new.failureCount ∧
  old.retryCount < new.retryCount

def applyGritOnStallFailure
    (trace : AffectInterruptTrace)
    (metric : GritMetric) : GritMetric :=
  if traceDegenerates trace then
    registerGritRetryAfterFailure metric
  else
    metric

/-- Beckett-style continuance: the system registers impossibility pressure and
    still records the next attempt. -/
structure BeckettContinuance where
  mustGoOn : Bool
  cannotGoOn : Bool
  goesOn : Bool
  deriving Repr, DecidableEq

def beckettGrit (state : BeckettContinuance) : Prop :=
  state.mustGoOn = true ∧ state.cannotGoOn = true ∧ state.goesOn = true

def affectStallState
    (old new : AffectMetric) : ContrarianStallIsOptimal.StallState :=
  { is_stalled := affectDegenerates old new
    is_optimal := affectDegenerates old new }

def affectOracleStallState (duration : Nat) : OracleStallState :=
  { stallDuration := duration
    metacognitiveDepth := duration
    stall_accelerates_metacognition := Nat.le_refl duration }

def dodgeballAffectInterruptValidates
    (tactic : DodgeballTactic) (trace : AffectInterruptTrace) : Prop :=
  isRefinementTactic tactic ∧ affectInterruptValidated trace

def stallCanBeUsed (trace : AffectInterruptTrace) : Prop :=
  traceDegenerates trace

theorem validated_interrupt_names_emotion
    {trace : AffectInterruptTrace} (h : affectInterruptValidated trace) :
    trace.namedEmotion = true := by
  exact h.1

theorem validated_interrupt_provides_space
    {trace : AffectInterruptTrace} (h : affectInterruptValidated trace) :
    trace.responseSpaceProvided = true := by
  exact h.2.1

theorem validated_interrupt_has_iteration
    {trace : AffectInterruptTrace} (h : affectInterruptValidated trace) :
    0 < trace.iterations := by
  exact h.2.2.1

theorem validated_interrupt_improves_affect
    {trace : AffectInterruptTrace} (h : affectInterruptValidated trace) :
    affectCost trace.final < affectCost trace.start := by
  exact h.2.2.2.1

theorem validated_interrupt_stabilizes_valence
    {trace : AffectInterruptTrace} (h : affectInterruptValidated trace) :
    trace.penultimate.valence = trace.final.valence := by
  exact h.2.2.2.2.1

theorem validated_interrupt_stabilizes_arousal
    {trace : AffectInterruptTrace} (h : affectInterruptValidated trace) :
    trace.penultimate.arousal = trace.final.arousal := by
  exact h.2.2.2.2.2

theorem missing_emotion_label_blocks_validation
    {trace : AffectInterruptTrace} (h : trace.namedEmotion = false) :
    ¬ affectInterruptValidated trace := by
  intro hValidated
  unfold affectInterruptValidated at hValidated
  rw [h] at hValidated
  cases hValidated.1

theorem missing_response_space_blocks_validation
    {trace : AffectInterruptTrace} (h : trace.responseSpaceProvided = false) :
    ¬ affectInterruptValidated trace := by
  intro hValidated
  unfold affectInterruptValidated at hValidated
  rw [h] at hValidated
  cases hValidated.2.1

theorem degeneration_allows_stall
    {trace : AffectInterruptTrace} (h : traceDegenerates trace) :
    stallCanBeUsed trace := by
  exact h

theorem improving_trace_not_degenerate
    {trace : AffectInterruptTrace} (h : traceImproves trace) :
    ¬ traceDegenerates trace := by
  intro hDegenerate
  exact Nat.lt_asymm h hDegenerate

theorem validated_interrupt_not_degenerate
    {trace : AffectInterruptTrace} (h : affectInterruptValidated trace) :
    ¬ traceDegenerates trace := by
  exact improving_trace_not_degenerate (validated_interrupt_improves_affect h)

theorem degenerating_trace_routes_stall
    {trace : AffectInterruptTrace} (h : traceDegenerates trace) :
    affectInterruptRoute trace = .degenerationStall := by
  unfold affectInterruptRoute
  simp [h]

theorem validated_trace_routes_refinement
    {trace : AffectInterruptTrace} (h : affectInterruptValidated trace) :
    affectInterruptRoute trace = .validatedRefinement := by
  unfold affectInterruptRoute
  simp [validated_interrupt_not_degenerate h, h]

theorem exponential_backoff_zero :
    exponentialBackoff 0 = 1 := by
  rfl

theorem exponential_backoff_failure_succ (failures : Nat) :
    exponentialBackoff (failures + 1) =
      2 * exponentialBackoff failures := by
  rfl

theorem register_stall_failure_increments
    (state : StallBackoffState) :
    (registerStallFailure state).failures = state.failures + 1 := by
  rfl

theorem register_stall_failure_preserves_base_delay
    (state : StallBackoffState) :
    (registerStallFailure state).baseDelay = state.baseDelay := by
  rfl

theorem register_stall_failure_preserves_base_silence
    (state : StallBackoffState) :
    (registerStallFailure state).baseSilence = state.baseSilence := by
  rfl

theorem register_stall_failure_doubles_delay
    (state : StallBackoffState) :
    stallBackoffDelay (registerStallFailure state) =
      2 * stallBackoffDelay state := by
  unfold stallBackoffDelay registerStallFailure
  simp [exponentialBackoff, Nat.mul_left_comm]

theorem register_stall_failure_doubles_response_silence
    (state : StallBackoffState) :
    responseSilenceBudget (registerStallFailure state) =
      2 * responseSilenceBudget state := by
  unfold responseSilenceBudget registerStallFailure
  simp [exponentialBackoff, Nat.mul_left_comm]

theorem cringe_vacuum_contains_response_silence
    (state : StallBackoffState) :
    responseSilenceBudget state ≤ cringeVacuum state := by
  unfold cringeVacuum
  exact Nat.le_add_right (responseSilenceBudget state) state.failures

theorem registered_failure_cringe_contains_doubled_silence
    (state : StallBackoffState) :
    2 * responseSilenceBudget state ≤
      cringeVacuum (registerStallFailure state) := by
  rw [← register_stall_failure_doubles_response_silence state]
  exact cringe_vacuum_contains_response_silence
    (registerStallFailure state)

theorem degenerating_trace_applies_stall_backoff
    {trace : AffectInterruptTrace} (state : StallBackoffState)
    (h : traceDegenerates trace) :
    applyStallBackoffOnFailure trace state =
      registerStallFailure state := by
  unfold applyStallBackoffOnFailure
  simp [h]

theorem nondegenerating_trace_preserves_stall_backoff
    {trace : AffectInterruptTrace} (state : StallBackoffState)
    (h : ¬ traceDegenerates trace) :
    applyStallBackoffOnFailure trace state = state := by
  unfold applyStallBackoffOnFailure
  simp [h]

theorem degenerating_trace_backoff_doubles_delay
    {trace : AffectInterruptTrace} (state : StallBackoffState)
    (h : traceDegenerates trace) :
    stallBackoffDelay (applyStallBackoffOnFailure trace state) =
      2 * stallBackoffDelay state := by
  rw [degenerating_trace_applies_stall_backoff state h]
  exact register_stall_failure_doubles_delay state

theorem degenerating_trace_backoff_doubles_response_silence
    {trace : AffectInterruptTrace} (state : StallBackoffState)
    (h : traceDegenerates trace) :
    responseSilenceBudget (applyStallBackoffOnFailure trace state) =
      2 * responseSilenceBudget state := by
  rw [degenerating_trace_applies_stall_backoff state h]
  exact register_stall_failure_doubles_response_silence state

theorem degenerating_trace_cringe_contains_doubled_silence
    {trace : AffectInterruptTrace} (state : StallBackoffState)
    (h : traceDegenerates trace) :
    2 * responseSilenceBudget state ≤
      cringeVacuum (applyStallBackoffOnFailure trace state) := by
  rw [degenerating_trace_applies_stall_backoff state h]
  exact registered_failure_cringe_contains_doubled_silence state

theorem register_grit_retry_increments_retry
    (metric : GritMetric) :
    (registerGritRetryAfterFailure metric).retryCount =
      metric.retryCount + 1 := by
  rfl

theorem register_grit_retry_increments_failure
    (metric : GritMetric) :
    (registerGritRetryAfterFailure metric).failureCount =
      metric.failureCount + 1 := by
  rfl

theorem register_grit_retry_is_continuance
    (metric : GritMetric) :
    continuanceInFaceOfFailure metric
      (registerGritRetryAfterFailure metric) := by
  constructor
  · exact Nat.lt_succ_self metric.failureCount
  · exact Nat.lt_succ_self metric.retryCount

theorem degenerating_trace_updates_grit_continuance
    {trace : AffectInterruptTrace} (metric : GritMetric)
    (h : traceDegenerates trace) :
    continuanceInFaceOfFailure metric
      (applyGritOnStallFailure trace metric) := by
  unfold applyGritOnStallFailure
  simp [h, register_grit_retry_is_continuance metric]

theorem beckett_grit_goes_on
    {state : BeckettContinuance} (h : beckettGrit state) :
    state.goesOn = true := by
  exact h.2.2

theorem degenerating_metrics_activate_stall
    {old new : AffectMetric} (h : affectDegenerates old new) :
    (affectStallState old new).is_stalled := by
  exact h

theorem degenerating_metrics_make_stall_optimal
    {old new : AffectMetric} (h : affectDegenerates old new) :
    (affectStallState old new).is_optimal := by
  exact ContrarianStallIsOptimal.stall_can_be_optimal
    (affectStallState old new) ⟨h, h⟩

theorem affect_stall_has_metacognitive_bound (duration : Nat) :
    (affectOracleStallState duration).stallDuration ≤
      (affectOracleStallState duration).metacognitiveDepth := by
  exact oracle_stall_induces_metacognitive_acceleration
    (affectOracleStallState duration)

theorem dodgeball_affect_interrupt_uses_refinement_tactic
    {tactic : DodgeballTactic} {trace : AffectInterruptTrace}
    (h : dodgeballAffectInterruptValidates tactic trace) :
    isRefinementTactic tactic := by
  exact h.1

theorem dodgeball_affect_interrupt_improves_affect
    {tactic : DodgeballTactic} {trace : AffectInterruptTrace}
    (h : dodgeballAffectInterruptValidates tactic trace) :
    affectCost trace.final < affectCost trace.start := by
  exact validated_interrupt_improves_affect h.2

end AffectLabelingPatternInterrupt
end Gnosis
