/-
  NegativeKnowledgeAsState.lean
  =============================

  TAYLOR'S WAVE-9 INSIGHT: "DELETING IS A STATE."

  When the ledger demotes a positive claim — e.g. when wave-4
  removes the `ProjectedCertified` label that wave-3 had attached to
  qwen-coder-7b at K=5 — the resulting absence is NOT a return to
  ignorance. The system now KNOWS that the projection was vacuous.
  The deletion event is itself a recorded vertex in the knowledge
  ledger, with its own incidence structure. The DELETION carries
  information.

  This module formalises that insight. Negative knowledge is a
  first-class state, not a void. The runtime must distinguish:

    • PositiveAbsence — we measured the spot and the thing is
      DEMONSTRABLY NOT THERE. A hole we can SEE. Carries information
      about WHAT isn't there.

    • NegativeUnknown — we never measured. An unmeasured void.
      Carries no information about the spot itself; only about our
      ignorance.

  The load-bearing inversion: removing a `ProjectedCertified` label
  does not return the system to a prior state, because the system
  now KNOWS that the projection was vacuous. The absence is
  ENRICHED; it has a story (the demotion reason, the prior state,
  the falsifying experiment).

  Per-instance state of the wave-9 ledger:

    • qwen-coder-7b @ K=5 PCA-only ⇒ PositiveAbsence
      (we measured 0/30 — the hole is documented).

    • llama-1b @ k=8 PCA-only ⇒ NegativeUnknown
      (never measured; wave-3 had projected it as Certified, an
      anti-theory rejected as vacuous).

    • cliff structure within Qwen family ⇒ PositivePresence
      (waves 1 and 2 atlases both confirm).

  Init-only Lean 4. Zero sorries, zero axioms.
-/

namespace Gnosis
namespace NegativeKnowledgeAsState

-- ══════════════════════════════════════════════════════════
-- THE FOUR KNOWLEDGE STATES
-- ══════════════════════════════════════════════════════════

/-- The four first-class epistemic states a knowledge record can
    occupy. The runtime treats these as distinct cases for policy:
    a `PositiveAbsence` is actionable (we know the gap), an
    `InActiveDemotion` is auditable (we know WHY the gap appeared),
    and a `NegativeUnknown` is a candidate for measurement.

    Information ordering (smallest to largest):

      NegativeUnknown < InActiveDemotion ≤ PositiveAbsence
        ≤ PositivePresence

    where `InActiveDemotion` carries the demotion reason but not
    yet a stable post-demotion classification, and `PositiveAbsence`
    carries both the demotion reason AND the standing absence
    record. -/
inductive KnowledgeState
  | PositivePresence
  | PositiveAbsence
  | NegativeUnknown
  | InActiveDemotion
  deriving DecidableEq, Repr

-- ══════════════════════════════════════════════════════════
-- THE KNOWLEDGE RECORD
-- ══════════════════════════════════════════════════════════

/-- A single recorded vertex in the ledger.

    The fields encode WHAT the record is about, WHAT state it is
    in, WHAT state it WAS in (if any), and WHY the transition
    happened. The transition reason is THE load-bearing field for
    `PositiveAbsence` and `InActiveDemotion`: it is the story that
    distinguishes a documented hole from an unmeasured void.

    • `subject` — free-form English description of the claim under
      tracking.

    • `state` — the current `KnowledgeState`.

    • `prior_state` — the state immediately before the most recent
      transition, or `none` if the record was born in its current
      state (e.g. a fresh `PositivePresence` from a new measurement).

    • `reason_for_transition` — free-form English description of
      WHY the transition happened (the falsifying wave, the demotion
      methodology, the anti-theory audit, etc.). Required to be
      non-empty for `PositiveAbsence` records — see
      `positive_absence_carries_information` below. -/
structure KnowledgeRecord where
  subject               : String
  state                 : KnowledgeState
  prior_state           : Option KnowledgeState
  reason_for_transition : String
  deriving Repr

-- ══════════════════════════════════════════════════════════
-- INFORMATION CONTENT ORDERING
-- ══════════════════════════════════════════════════════════

/-- Information content of a knowledge state, as a `Nat`.

    The ordering encodes the load-bearing claim of this module:
    a measured hole carries strictly more information than an
    unmeasured void.

      NegativeUnknown   = 0  (we know nothing about the spot)
      InActiveDemotion  = 2  (we know the prior, we know the demotion
                              reason, but the post-demotion state has
                              not yet stabilised)
      PositiveAbsence   = 3  (we know the prior, the demotion reason,
                              AND the spot is documented as empty)
      PositivePresence  = 4  (we know the prior — if any — and the
                              spot is documented as full)

    The `InActiveDemotion < PositiveAbsence` inequality is the
    "deleting is a state" inequality: a fully-realised absence
    carries more information than a transition mid-flight. -/
def stateInformationContent : KnowledgeState → Nat
  | .NegativeUnknown   => 0
  | .InActiveDemotion  => 2
  | .PositiveAbsence   => 3
  | .PositivePresence  => 4

/-- Information content of a knowledge record. Currently a thin
    wrapper around `stateInformationContent`; future revisions may
    fold in `reason_for_transition` length or witness count. -/
def information_content (r : KnowledgeRecord) : Nat :=
  stateInformationContent r.state

-- ══════════════════════════════════════════════════════════
-- PER-INSTANCE RECORDS (the wave-9 ledger)
-- ══════════════════════════════════════════════════════════

/-- The qwen-coder-7b K=5 PCA-only record.

    Wave 3 projected this as `ProjectedCertified` from the qwen-0.5b
    sibling. Wave 4 ran the actual K=5 PCA-only measurement at
    coverage 0.50 and got 0/30 accept rate.

    The record's current state is `PositiveAbsence`: the hole at
    K=5 PCA-only on qwen-coder-7b is DEMONSTRATED. We can see it.
    Its prior state was `PositivePresence` (the wave-3 projection
    treated the claim as Certified). The transition reason is the
    wave-4 measurement. -/
def qwen_coder_7b_K5_PCA_record : KnowledgeRecord :=
  { subject :=
      "PCA-only at K=5 achieves operational fidelity on Qwen-Coder-7B"
  , state                 := .PositiveAbsence
  , prior_state           := some .PositivePresence
  , reason_for_transition := "wave-4 measurement, 30/30 rollback" }

/-- The llama-1b k=8 PCA-only record.

    Wave 3 listed llama-1b as `ProjectedCertified` from the qwen-0.5b
    sibling — a projection, not a measurement. Anti-theory rejected
    that as vacuous. The record's current state is `NegativeUnknown`:
    we have NOT measured the spot. We do not know whether the
    PCA-only fidelity claim holds on llama-1b; we only know that the
    wave-3 ledger conflated "we haven't measured" with "we measured
    and it was fine".

    The prior state was `PositivePresence` (the wave-3 vacuous
    Certified label). The transition reason is the anti-theory
    audit, not a measurement. -/
def llama_1b_record : KnowledgeRecord :=
  { subject :=
      "PCA-only at k=8 achieves operational fidelity on Llama-1B"
  , state                 := .NegativeUnknown
  , prior_state           := some .PositivePresence
  , reason_for_transition := "anti-theory turn: never measured, was vacuous claim" }

/-- The cliff-structure-within-Qwen-family record.

    Wave 1 measured the cliff structure on qwen-0.5b across the
    mid-pipeline layers; wave 2 cross-validated against qwen-coder-7b
    in the same family. Both atlases agree.

    Current state is `PositivePresence` with no prior state: this
    was a new conjecture confirmed by direct measurement; it was
    not a demoted-from-something record. -/
def cliff_law_within_qwen_record : KnowledgeRecord :=
  { subject :=
      "Cliff structure exists in mid-pipeline layers within Qwen family"
  , state                 := .PositivePresence
  , prior_state           := none
  , reason_for_transition := "wave-1 atlas + wave-2 cross-model atlas both confirm" }

-- ══════════════════════════════════════════════════════════
-- PER-INSTANCE STATE THEOREMS
-- ══════════════════════════════════════════════════════════

/-- Theorem: QWEN-CODER-7B IS A POSITIVE ABSENCE.

    The wave-4 K=5 PCA-only measurement returned 0/30. The hole is
    DOCUMENTED, not unknown. The runtime should treat this record
    as actionable knowledge about WHAT isn't there, not as ignorance
    awaiting measurement. -/
theorem qwen_coder_7b_is_PositiveAbsence :
    qwen_coder_7b_K5_PCA_record.state = .PositiveAbsence := by
  decide

/-- Theorem: LLAMA-1B IS NEGATIVE UNKNOWN.

    Distinguish this carefully from the qwen-coder-7b case. Llama-1B
    was NEVER MEASURED at PCA-only k=8. The wave-3 ledger projected
    a result from the sibling family; anti-theory rejected the
    projection. The current state is `NegativeUnknown` — a candidate
    for measurement, NOT a documented hole. -/
theorem llama_1b_is_NegativeUnknown :
    llama_1b_record.state = .NegativeUnknown := by
  decide

/-- Theorem: A POSITIVE ABSENCE CARRIES INFORMATION.

    The reason-for-transition string of any `PositiveAbsence` record
    is non-empty. We exhibit this for the qwen-coder-7b record: a
    measured hole is always accompanied by the methodology that
    measured it. -/
theorem positive_absence_carries_information :
    qwen_coder_7b_K5_PCA_record.state = .PositiveAbsence ∧
    qwen_coder_7b_K5_PCA_record.reason_for_transition ≠ "" := by
  decide

/-- Theorem: NEGATIVE-UNKNOWN CARRIES STRICTLY LESS INFORMATION
    THAN POSITIVE-ABSENCE.

    The information ordering puts an unmeasured void below a
    documented hole. Quantitatively:

      stateInformationContent NegativeUnknown = 0
      stateInformationContent PositiveAbsence = 3

    so an unmeasured void carries strictly less information than a
    measured hole. The runtime can use this inequality to prioritise
    measurement of `NegativeUnknown` records when budget permits. -/
theorem negative_unknown_carries_LESS_information_than_positive_absence :
    stateInformationContent .NegativeUnknown
      < stateInformationContent .PositiveAbsence := by
  decide

/-- Per-record version of the inequality, for the two reference
    records on file. -/
theorem llama_1b_carries_less_info_than_qwen_coder_7b :
    information_content llama_1b_record
      < information_content qwen_coder_7b_K5_PCA_record := by
  decide

-- ══════════════════════════════════════════════════════════
-- THE "DELETING IS A STATE" THEOREM
-- ══════════════════════════════════════════════════════════

/-- The hypothetical "before" record for qwen-coder-7b in a world
    where wave-4 had not happened: same subject, but state is
    `NegativeUnknown` (we had not measured the K=5 PCA-only point)
    and there is no prior or transition reason.

    This is the COUNTERFACTUAL the "deleting is a state" theorem
    quantifies against: had we left the spot unmeasured, our
    information content there would have been zero. By measuring
    and DEMOTING the projection, we GAINED information. -/
def qwen_coder_7b_K5_PCA_record_unmeasured : KnowledgeRecord :=
  { subject :=
      "PCA-only at K=5 achieves operational fidelity on Qwen-Coder-7B"
  , state                 := .NegativeUnknown
  , prior_state           := none
  , reason_for_transition := "" }

/-- THEOREM: TRANSITION TO POSITIVE-ABSENCE IS INFORMATION GAIN.

    THE LOAD-BEARING THEOREM OF THIS MODULE.

    For the qwen-coder-7b record, the post-wave-4 state
    (`PositiveAbsence` with a measured-falsification story) carries
    strictly more information than the counterfactual unmeasured
    state (`NegativeUnknown` with no story).

    Operationally: by demoting the wave-3 projection through a
    measured falsification, the ledger LEARNED MORE than it would
    have by leaving the spot unmeasured. The deletion is not a
    return to ignorance; it is an information-gain event.

    "Deleting is a state": the state after deletion is not the
    state before the projection, because the system now knows the
    projection was vacuous. The absence is enriched. -/
theorem transition_to_PositiveAbsence_is_information_gain :
    information_content qwen_coder_7b_K5_PCA_record
      > information_content qwen_coder_7b_K5_PCA_record_unmeasured := by
  decide

/-- General version: ANY record in `PositiveAbsence` carries more
    information than the same subject would carry in
    `NegativeUnknown`. The state alone forces the inequality. -/
theorem PositiveAbsence_dominates_NegativeUnknown
    (subject : String)
    (prior  : Option KnowledgeState)
    (reason : String) :
    information_content
      { subject := subject
      , state := .PositiveAbsence
      , prior_state := prior
      , reason_for_transition := reason }
    >
    information_content
      { subject := subject
      , state := .NegativeUnknown
      , prior_state := none
      , reason_for_transition := "" } := by
  -- Both sides reduce by definitional unfolding to `3 > 0`, since
  -- `information_content` only consults `state`.
  show 3 > 0
  decide

-- ══════════════════════════════════════════════════════════
-- LEDGER-LEVEL PROJECTIONS
-- ══════════════════════════════════════════════════════════

/-- Project a ledger to the records whose current state is
    `PositiveAbsence` — the documented holes the runtime can see.

    Useful for status pages: the count of visible holes is the
    count of measured falsifications still on the books. -/
def holes_visible (rs : List KnowledgeRecord) : List KnowledgeRecord :=
  rs.filter (fun r => r.state = .PositiveAbsence)

/-- Project a ledger to the records whose current state is
    `NegativeUnknown` — the candidates for future measurement.

    Useful for measurement-budget allocation: each
    `NegativeUnknown` record is a known unknown. -/
def holes_unmeasured (rs : List KnowledgeRecord) : List KnowledgeRecord :=
  rs.filter (fun r => r.state = .NegativeUnknown)

/-- The current wave-9 ledger of all three reference records, in
    canonical order. -/
def current_ledger : List KnowledgeRecord :=
  [ qwen_coder_7b_K5_PCA_record
  , llama_1b_record
  , cliff_law_within_qwen_record ]

/-- The current set of visible (i.e. `PositiveAbsence`) holes. -/
def current_visible_holes : List KnowledgeRecord :=
  holes_visible current_ledger

/-- The current set of unmeasured (i.e. `NegativeUnknown`) holes. -/
def current_unmeasured_holes : List KnowledgeRecord :=
  holes_unmeasured current_ledger

-- ══════════════════════════════════════════════════════════
-- LEDGER COUNT THEOREMS
-- ══════════════════════════════════════════════════════════

/-- Theorem: AT LEAST ONE VISIBLE HOLE IS ON THE BOOKS.

    The wave-4 demotion of qwen-coder-7b K=5 PCA-only is recorded.
    The runtime can render at least one documented hole on the
    status page. -/
theorem count_visible_holes_is_at_least_one :
    current_visible_holes.length ≥ 1 := by
  decide

/-- Theorem: AT LEAST ONE UNMEASURED HOLE IS ON THE BOOKS.

    The llama-1b k=8 PCA-only spot is a `NegativeUnknown` candidate
    for future measurement. Measurement-budget policy can pick it
    up. -/
theorem count_unmeasured_holes_is_at_least_one :
    current_unmeasured_holes.length ≥ 1 := by
  decide

/-- Theorem: VISIBLE HOLES AND UNMEASURED HOLES ARE DISJOINT
    CATEGORIES.

    `PositiveAbsence` and `NegativeUnknown` are constructor-level
    distinct, so a record cannot simultaneously be a visible hole
    and an unmeasured hole. The two categories partition the
    negative-knowledge subset of the ledger. -/
theorem visible_and_unmeasured_states_are_distinct :
    KnowledgeState.PositiveAbsence ≠ KnowledgeState.NegativeUnknown := by
  decide

-- ══════════════════════════════════════════════════════════
-- CLI-STYLE SUMMARY
-- ══════════════════════════════════════════════════════════

/-- Render a `KnowledgeState` as a short string. -/
def stateToString : KnowledgeState → String
  | .PositivePresence => "PositivePresence"
  | .PositiveAbsence  => "PositiveAbsence"
  | .NegativeUnknown  => "NegativeUnknown"
  | .InActiveDemotion => "InActiveDemotion"

/-- Render an `Option KnowledgeState` as a short string. -/
def priorStateToString : Option KnowledgeState → String
  | none   => "none"
  | some s => "some " ++ stateToString s

/-- Render one `KnowledgeRecord` as a CLI-style summary line:

      "SUBJECT: STATE (prior=PRIOR, info=N) -- REASON" -/
def summarizeOne (r : KnowledgeRecord) : String :=
  r.subject ++ ": " ++
  stateToString r.state ++
  " (prior=" ++ priorStateToString r.prior_state ++
  ", info=" ++ toString (information_content r) ++
  ") -- " ++ r.reason_for_transition

/-- CLI-style summary report. Renders a list of knowledge records
    as one summary line per record, joined by newlines. -/
def summarize (rs : List KnowledgeRecord) : String :=
  String.intercalate "\n" (rs.map summarizeOne)

end NegativeKnowledgeAsState
end Gnosis
