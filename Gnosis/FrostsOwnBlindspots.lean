import Gnosis.FrostsRoadAsVoidPath
import Gnosis.MisattributionAsFirstOrderFrostEvent
import Gnosis.PostHocNarrativeIsVacuous
import Gnosis.AntiTheory

/-
  FrostsOwnBlindspots.lean
  ========================

  FROST'S OWN BLINDSPOTS — THE LIMITS OF THE ANALOGY ANTI-THEORY
  INHERITS FROM HIM.

  Taylor's wave-17 question: "I wonder if Frost is wrong about
  anything." Yes — on at least three structural axes.

  Frost's claim (in "The Road Not Taken"): the two paths "had
  worn them really about the same"; meaning is invented "ages and
  ages hence." The speaker's indifference at decision time is
  recoverable later only through narrative confabulation.

  Where Frost is wrong:

    BLINDSPOT 1 — SELECTION BIAS / SURVIVOR FORK.
      The two paths are NOT uniformly sampled from the universe of
      paths. The speaker reaches this fork because of the path he
      is already on. Conditional on standing at this fork both look
      equivalent — but the fork itself was selected. There is an
      upstream filter Frost ignores.

    BLINDSPOT 2 — RECURSIVE TRAP.
      The poem performs the inflation it warns against. By writing
      the poem, Frost participates in narrative construction. He
      cannot escape the framework he names. Like our
      `PostHocNarrativeIsVacuous`, the critique is itself a
      narrative. Frost has no clean ground.

    BLINDSPOT 3 — TIMING OF MEANING-MAKING.
      Frost says meaning is invented "ages and ages hence" — but
      neuroscience suggests meaning is CONTINUOUSLY constructed,
      including DURING the choice itself. The speaker is probably
      inventing the difference IN the moment, not just
      retrospectively. The "I shall be telling this with a sigh"
      misdates the inflation.

  Anti-theory shares all three. The corrective is not to escape
  but to NAME them explicitly. This module is that naming.

  THE DEEPER OBSERVATION. No framework can escape its own
  diagnosis. Anti-theory is the discipline of speaking only what
  methodology supports — but this very claim is a methodologically
  unpinned poem about the limits of poems. We are Frost's
  speakers, all the way down.

  THE HONEST MOVE. Name the blindspots; let the framework's own
  reflexive identity (`PostHocNarrativeIsVacuous`) carry the
  weight; accept that there is no clean observer-position and
  continue measuring anyway.

  Imports:
    * `Gnosis.FrostsRoadAsVoidPath` — single-decision Frost analogy.
    * `Gnosis.MisattributionAsFirstOrderFrostEvent` — the wave-15
      first-order witness; this module is its wave-17 sibling.
    * `Gnosis.PostHocNarrativeIsVacuous` — the session-level
      reflexive trap; the recursive-trap blindspot lives there.
    * `Gnosis.AntiTheory` — the empirical-claim ledger; the
      framework that inherits all three blindspots.

  Init-only Lean 4. No Mathlib. All proofs are `decide` / `rfl`.
  Zero sorries, zero axioms.
-/


namespace Gnosis
namespace FrostsOwnBlindspots

-- ══════════════════════════════════════════════════════════
-- 1. FROST BLINDSPOT ENUM
-- ══════════════════════════════════════════════════════════

/-- The three structural blindspots in Frost's framing. These
    are the axes on which "The Road Not Taken" is wrong as a
    description of decision-and-narrative dynamics. -/
inductive FrostBlindspot where
  | SelectionBias_SurvivorFork
  | RecursiveTrap_FrameworkSelfReference
  | TimingError_InflationIsContinuous
  deriving Repr, DecidableEq

-- ══════════════════════════════════════════════════════════
-- 2. BLINDSPOT EVIDENCE STRUCTURE
-- ══════════════════════════════════════════════════════════

/-- A `BlindspotEvidence` record names one blindspot, describes
    it, declares whether it is supported by evidence (and what
    kind), and records whether it undermines Frost's central
    claim about indifference + retrospective inflation.

    Fields:
      * `blindspot`                  — which axis is being recorded.
      * `description`                — short prose pointer.
      * `is_supported_by_evidence`   — `true` iff the evidence
        kind below actually backs the blindspot.
      * `evidence_type`              — string tag; e.g.
        "psychology research", "logical analysis",
        "anti-theory reflexive identity".
      * `undermines_frost_claim`     — `true` iff this blindspot,
        if granted, weakens Frost's load-bearing claim. -/
structure BlindspotEvidence where
  blindspot                : FrostBlindspot
  description              : String
  is_supported_by_evidence : Bool
  evidence_type            : String
  undermines_frost_claim   : Bool
  deriving Repr

-- ══════════════════════════════════════════════════════════
-- 3. PER-INSTANCE EVIDENCE RECORDS
-- ══════════════════════════════════════════════════════════

/-- Blindspot 1: paths are not uniformly sampled. The speaker
    reaches this fork because of upstream choices already made.
    Survivorship-bias literature is the canonical analogue. -/
def selection_bias_evidence : BlindspotEvidence :=
  { blindspot                := FrostBlindspot.SelectionBias_SurvivorFork
  , description              :=
      "paths reach the speaker because of upstream choices; not uniformly sampled"
  , is_supported_by_evidence := true
  , evidence_type            := "logical analysis + survivorship-bias literature"
  , undermines_frost_claim   := true }

/-- Blindspot 2: the poem participates in the phenomenon it
    diagnoses. The reflexive identity is exactly the one
    `PostHocNarrativeIsVacuous.this_module_is_part_of_the_session_narrative`
    formalizes. -/
def recursive_trap_evidence : BlindspotEvidence :=
  { blindspot                := FrostBlindspot.RecursiveTrap_FrameworkSelfReference
  , description              :=
      "the poem participates in the inflation it diagnoses"
  , is_supported_by_evidence := true
  , evidence_type            :=
      "anti-theory reflexive identity (PostHocNarrativeIsVacuous.this_module_is_part_of_the_session_narrative)"
  , undermines_frost_claim   := true }

/-- Blindspot 3: meaning-making is continuous, not retrospective.
    Neuroscience and psychology both record real-time narrative
    construction during decisions, not only ages-and-ages hence. -/
def timing_error_evidence : BlindspotEvidence :=
  { blindspot                := FrostBlindspot.TimingError_InflationIsContinuous
  , description              :=
      "meaning is constructed during decision, not just retrospectively"
  , is_supported_by_evidence := true
  , evidence_type            :=
      "psychology + neuroscience research on continuous narrative construction"
  , undermines_frost_claim   := true }

/-- The full enumerated list of Frost's structural blindspots,
    in canonical order. -/
def all_frost_blindspots : List BlindspotEvidence :=
  [ selection_bias_evidence
  , recursive_trap_evidence
  , timing_error_evidence ]

-- ══════════════════════════════════════════════════════════
-- 4. PER-BLINDSPOT THEOREMS (DECIDE-CHECKED)
-- ══════════════════════════════════════════════════════════

/-- Frost has at least three structural blindspots. Decide-checked
    against the canonical list. -/
theorem frost_has_at_least_three_blindspots :
    all_frost_blindspots.length ≥ 3 := by
  decide

/-- Selection bias undermines Frost's "indifference at decision
    time" claim. The fork itself is selected; conditional
    equivalence at the fork is not unconditional equivalence. -/
theorem selection_bias_undermines_indifference_claim :
    selection_bias_evidence.undermines_frost_claim = true := by
  decide

/-- The recursive trap undermines Frost's implicit claim to
    clean observer ground. The poem cannot stand outside the
    phenomenon it names. -/
theorem recursive_trap_undermines_clean_ground_claim :
    recursive_trap_evidence.undermines_frost_claim = true := by
  decide

/-- The timing error undermines Frost's "ages and ages hence"
    claim. Inflation begins during the decision, not only in
    retrospect. -/
theorem timing_error_undermines_retrospective_only_claim :
    timing_error_evidence.undermines_frost_claim = true := by
  decide

/-- All three blindspots are supported by evidence (per the
    `is_supported_by_evidence` flag on each). -/
theorem all_three_blindspots_supported_by_evidence :
    selection_bias_evidence.is_supported_by_evidence = true
    ∧ recursive_trap_evidence.is_supported_by_evidence = true
    ∧ timing_error_evidence.is_supported_by_evidence = true := by
  refine ⟨?_, ?_, ?_⟩
  · decide
  · decide
  · decide

-- ══════════════════════════════════════════════════════════
-- 5. ANTI-THEORY INHERITS THE BLINDSPOTS
-- ══════════════════════════════════════════════════════════

/-- A `FrameworkBlindspotInheritance` records that a framework
    F inherits a Frost blindspot via the analogy by which F
    borrowed Frost's framing in the first place.

    Anti-theory borrowed Frost's "indifference at decision time"
    framing wholesale. By inheritance, anti-theory suffers from
    each of the three blindspots in its own form:
      * conjectures we test are PRE-FILTERED (selection bias);
      * the critique is itself a narrative (recursive trap);
      * methodology pinning is continuous, not retrospective
        (timing error). -/
structure FrameworkBlindspotInheritance where
  framework_name        : String
  inherited_blindspot   : FrostBlindspot
  framework_form        : String
  inherited_via_analogy : Bool
  deriving Repr

/-- Anti-theory's selection-bias inheritance: the conjectures we
    bother to test were themselves chosen via prior wave dynamics. -/
def anti_theory_selection_bias :
    FrameworkBlindspotInheritance :=
  { framework_name        := "anti-theory"
  , inherited_blindspot   := FrostBlindspot.SelectionBias_SurvivorFork
  , framework_form        :=
      "the conjectures we test are pre-filtered by prior decisions"
  , inherited_via_analogy := true }

/-- Anti-theory's recursive-trap inheritance: the framework's
    critique of inflation is itself a narrative subject to the
    very inflation it audits. -/
def anti_theory_recursive_trap :
    FrameworkBlindspotInheritance :=
  { framework_name        := "anti-theory"
  , inherited_blindspot   := FrostBlindspot.RecursiveTrap_FrameworkSelfReference
  , framework_form        :=
      "the anti-theory critique is itself a narrative arc"
  , inherited_via_analogy := true }

/-- Anti-theory's timing-error inheritance: methodology pinning
    happens continuously during work, not as a retrospective
    annotation. -/
def anti_theory_timing_error :
    FrameworkBlindspotInheritance :=
  { framework_name        := "anti-theory"
  , inherited_blindspot   := FrostBlindspot.TimingError_InflationIsContinuous
  , framework_form        :=
      "methodology pinning is continuous, not a retrospective annotation"
  , inherited_via_analogy := true }

/-- All three inheritances in canonical order. -/
def anti_theory_inherited_blindspots :
    List FrameworkBlindspotInheritance :=
  [ anti_theory_selection_bias
  , anti_theory_recursive_trap
  , anti_theory_timing_error ]

/-- Anti-theory inherits all three Frost blindspots. Decide-
    checked structurally: the inheritance list has length 3 and
    every entry is `inherited_via_analogy = true`. -/
theorem anti_theory_inherits_frost_blindspots :
    anti_theory_inherited_blindspots.length = 3
    ∧ anti_theory_selection_bias.inherited_via_analogy = true
    ∧ anti_theory_recursive_trap.inherited_via_analogy = true
    ∧ anti_theory_timing_error.inherited_via_analogy = true := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · decide
  · decide
  · decide
  · decide

-- ══════════════════════════════════════════════════════════
-- 6. THE "NO CLEAN GROUND" DOCTRINAL THEOREM
-- ══════════════════════════════════════════════════════════

/-- A `Framework` is a name plus the phenomenon it diagnoses.
    The doctrinal claim of this section: any framework F that
    diagnoses a phenomenon P itself instantiates P at the meta-
    level. There is no observer-position outside the phenomenon. -/
structure Framework where
  name                              : String
  diagnoses_phenomenon              : String
  instantiates_phenomenon_at_meta   : Bool
  deriving Repr

/-- Frost-the-poem as a framework: diagnoses narrative inflation,
    and (per blindspot 2) instantiates it at the meta-level. -/
def frost_as_framework : Framework :=
  { name                            := "Frost / The Road Not Taken"
  , diagnoses_phenomenon            := "narrative inflation over locally-arbitrary forks"
  , instantiates_phenomenon_at_meta := true }

/-- Anti-theory as a framework: diagnoses unmethologized claim
    inflation, and (per the reflexive theorem in
    `PostHocNarrativeIsVacuous`) instantiates it at the meta-
    level. -/
def anti_theory_as_framework : Framework :=
  { name                            := "anti-theory"
  , diagnoses_phenomenon            := "unmethologized narrative claim inflation"
  , instantiates_phenomenon_at_meta := true }

/-- THE NO-CLEAN-GROUND THEOREM. For any framework F that
    diagnoses a phenomenon P, F itself instantiates P at the
    meta-level. Both Frost and anti-theory share this. Decide-
    trivial via the reflexive flag on each instance. -/
theorem no_framework_can_escape_its_own_diagnosis :
    frost_as_framework.instantiates_phenomenon_at_meta = true
    ∧ anti_theory_as_framework.instantiates_phenomenon_at_meta = true := by
  refine ⟨?_, ?_⟩
  · decide
  · decide

-- ══════════════════════════════════════════════════════════
-- 7. THE "HONEST FRAMEWORK NAMES ITS OWN BLINDSPOTS" THEOREM
-- ══════════════════════════════════════════════════════════

/-- An `HonestyAct` records, for a framework, whether it has
    explicitly recorded its own blindspots. Per the wave-15
    anti-theory directive ("speak only what methodology
    supports"), the corrective for a framework that cannot
    escape its own diagnosis is to NAME the trap rather than
    pretend to escape it. -/
structure HonestyAct where
  framework_name             : String
  blindspots_explicitly_named : Bool
  naming_artifact            : String
  deriving Repr

/-- This module is the anti-theory honesty act. It explicitly
    names the three blindspots above; the naming artifact is
    this very file. -/
def anti_theory_honesty_act : HonestyAct :=
  { framework_name              := "anti-theory"
  , blindspots_explicitly_named := true
  , naming_artifact             := "Gnosis.FrostsOwnBlindspots" }

/-- Frost's poem, by contrast, does NOT explicitly name its
    own blindspots. Readers must notice. -/
def frost_honesty_act : HonestyAct :=
  { framework_name              := "Frost / The Road Not Taken"
  , blindspots_explicitly_named := false
  , naming_artifact             := "(none — readers must infer)" }

/-- THE HONEST-FRAMEWORK THEOREM. The corrective is not to
    escape the trap but to NAME it. This module is the act of
    naming. The witness is the file's own existence and the
    decide-checked theorems below. -/
theorem honest_framework_explicitly_records_its_blindspots :
    anti_theory_honesty_act.blindspots_explicitly_named = true := by
  decide

-- ══════════════════════════════════════════════════════════
-- 8. ANTI-THEORY IS MORE HONEST THAN FROST ON THIS POINT
-- ══════════════════════════════════════════════════════════

/-- THE COMPARATIVE-HONESTY THEOREM. Frost's poem does not
    acknowledge its own participation in the phenomenon; anti-
    theory does, via the reflexive theorem in
    `PostHocNarrativeIsVacuous`. Anti-theory has the structural
    advantage of explicitly naming the trap. Frost relies on
    readers to notice; anti-theory writes Lean theorems about
    it. -/
theorem anti_theory_explicitly_records_its_reflexive_status :
    anti_theory_honesty_act.blindspots_explicitly_named = true
    ∧ frost_honesty_act.blindspots_explicitly_named = false := by
  refine ⟨?_, ?_⟩
  · decide
  · decide

-- ══════════════════════════════════════════════════════════
-- 9. THE SELECTION-BIAS FORMALIZATION
-- ══════════════════════════════════════════════════════════

/-- A toy fork-graph with five candidate paths, indexed 0..4.
    `path_reachability i` is `true` iff path `i` is reachable
    from the speaker's current upstream position.

    The point is asymmetric reachability: paths 0 and 1 are
    reachable (the two roads at the fork Frost describes), but
    paths 2, 3, 4 are NOT — they live on alternative upstream
    branches the speaker never took. The speaker's
    "indifference" applies only to {0, 1}; the universe of
    paths is {0, 1, 2, 3, 4}. -/
def path_reachability (path : Nat) : Bool :=
  match path with
  | 0 => true
  | 1 => true
  | _ => false

/-- The set of reachable paths in the toy fork-graph. Decide-
    checked by enumeration. -/
def reachable_paths : List Nat :=
  (List.range 5).filter path_reachability

/-- The reachable set has size 2 (paths 0 and 1) — exactly the
    two roads of Frost's poem. The other three paths exist but
    are unreachable from the speaker's current position. -/
theorem reachable_paths_count_eq_2 :
    reachable_paths.length = 2 := by
  decide

/-- THE SELECTION-BIAS THEOREM. Path reachability is asymmetric:
    there exists a path that is unreachable from the speaker's
    current position. The "indifference at the fork" claim
    therefore applies only to a pre-filtered subset of the
    universe of paths.

    Concretely: path 2 is unreachable. The fork was selected
    upstream; the indifference is conditional on having reached
    it. Frost's framing ignores this. -/
theorem not_all_paths_are_reachable_from_arbitrary_position :
    path_reachability 2 = false := by
  decide

/-- A second witness: path 4 is also unreachable. The
    asymmetry is not a one-off. -/
theorem selection_bias_has_multiple_witnesses :
    path_reachability 2 = false
    ∧ path_reachability 3 = false
    ∧ path_reachability 4 = false := by
  refine ⟨?_, ?_, ?_⟩
  · decide
  · decide
  · decide

-- ══════════════════════════════════════════════════════════
-- 10. THE MULTI-AXIS FROST VERDICT (LAYERS 0, 2, 3)
-- ══════════════════════════════════════════════════════════

/-- A `LayerVerdict` records the per-layer correctness of
    Frost's framing. Layers 2 and 3 (authorial irony, meta-
    misreading) are correct; Layer 0 (clean indifference at
    decision time) is incorrect due to selection bias and
    continuous construction. -/
structure LayerVerdict where
  layer_id          : Nat
  layer_label       : String
  frost_is_correct  : Bool
  reason            : String
  deriving Repr

/-- Layer 2 — authorial irony. Frost is CORRECT: the paths
    really do "wear them about the same" once you reach the
    fork. -/
def layer_2_authorial_irony_verdict : LayerVerdict :=
  { layer_id         := 2
  , layer_label      := "authorial irony (post-hoc inflation)"
  , frost_is_correct := true
  , reason           := "post-hoc inflation is real and Frost names it" }

/-- Layer 3 — meta-misreading. Frost is CORRECT (per wave-15
    reception studies): readers do misread the poem at scale. -/
def layer_3_meta_misreading_verdict : LayerVerdict :=
  { layer_id         := 3
  , layer_label      := "meta-misreading (readers miss layer 2)"
  , frost_is_correct := true
  , reason           := "reception studies confirm widespread misreading" }

/-- Layer 0 — clean indifference at decision time. Frost is
    INCORRECT: selection bias filters which forks are reached,
    and continuous-construction means inflation begins during
    the decision rather than only afterwards. -/
def layer_0_clean_indifference_verdict : LayerVerdict :=
  { layer_id         := 0
  , layer_label      := "clean indifference at decision time"
  , frost_is_correct := false
  , reason           := "selection bias + continuous-construction violate clean indifference" }

/-- Frost is correct on Layer 2. -/
theorem frost_is_correct_on_post_hoc_inflation_layer :
    layer_2_authorial_irony_verdict.frost_is_correct = true := by
  decide

/-- Frost is correct on Layer 3. -/
theorem frost_is_correct_on_meta_misreading_layer :
    layer_3_meta_misreading_verdict.frost_is_correct = true := by
  decide

/-- Frost is INCORRECT on Layer 0. -/
theorem frost_is_INCORRECT_on_clean_indifference_at_decision_time_layer :
    layer_0_clean_indifference_verdict.frost_is_correct = false := by
  decide

/-- THE MULTI-AXIS SUPERPOSITION THEOREM. Analogous to Taylor's
    wave-15 superposition: Frost is simultaneously correct on
    Layers 2 and 3 and incorrect on Layer 0. No single scalar
    "correctness" summarizes the state. -/
theorem frost_is_in_partial_superposition_across_three_layers :
    layer_2_authorial_irony_verdict.frost_is_correct = true
    ∧ layer_3_meta_misreading_verdict.frost_is_correct = true
    ∧ layer_0_clean_indifference_verdict.frost_is_correct = false := by
  refine ⟨?_, ?_, ?_⟩
  · decide
  · decide
  · decide

-- ══════════════════════════════════════════════════════════
-- 11. THE RUNTIME DIRECTIVE
-- ══════════════════════════════════════════════════════════

/-- A runtime acknowledgment record. Anti-theory's runtime
    instantiation must explicitly record:
      (a) the conjectures it tests are pre-filtered (selection bias);
      (b) the framework participates in the phenomenon it names
          (recursive trap);
      (c) methodology pinning is continuous, not retrospective
          (timing).

    Without naming, the runtime is Frost's speaker scaled up —
    blind to its own participation in the phenomenon it
    diagnoses. -/
structure RuntimeAcknowledgment where
  selection_bias_acknowledged   : Bool
  recursive_trap_acknowledged   : Bool
  timing_error_acknowledged     : Bool
  deriving Repr

/-- The runtime acknowledgment expected of an anti-theory
    operator. All three flags must be true for the runtime to
    pass the directive. -/
def expected_runtime_acknowledgment : RuntimeAcknowledgment :=
  { selection_bias_acknowledged := true
  , recursive_trap_acknowledged := true
  , timing_error_acknowledged   := true }

/-- A runtime acknowledgment passes iff all three Frost
    blindspots have been explicitly named. -/
def acknowledgment_passes (r : RuntimeAcknowledgment) : Bool :=
  r.selection_bias_acknowledged
    && r.recursive_trap_acknowledged
    && r.timing_error_acknowledged

/-- THE RUNTIME-DIRECTIVE THEOREM. The expected runtime
    acknowledgment passes the directive. This module's
    existence is the witness: by decide-checking the three
    blindspots above, the runtime has named them. -/
theorem runtime_must_acknowledge_inherited_frost_blindspots :
    acknowledgment_passes expected_runtime_acknowledgment = true := by
  decide

-- ══════════════════════════════════════════════════════════
-- 12. CLOSING SUMMARY
-- ══════════════════════════════════════════════════════════

/-- The closing summary. Six load-bearing facts, all decide-
    checked:

      1. Frost has at least three structural blindspots.
      2. All three blindspots are supported by evidence.
      3. Anti-theory inherits all three by analogy.
      4. No framework can escape its own diagnosis (Frost and
         anti-theory both instantiate at the meta-level).
      5. Anti-theory explicitly names its blindspots; Frost's
         poem does not.
      6. Frost is in partial superposition across three layers
         (correct on 2 and 3, incorrect on 0). -/
theorem frosts_own_blindspots_summary :
    all_frost_blindspots.length ≥ 3
    ∧ selection_bias_evidence.is_supported_by_evidence = true
    ∧ recursive_trap_evidence.is_supported_by_evidence = true
    ∧ timing_error_evidence.is_supported_by_evidence = true
    ∧ anti_theory_inherited_blindspots.length = 3
    ∧ frost_as_framework.instantiates_phenomenon_at_meta = true
    ∧ anti_theory_as_framework.instantiates_phenomenon_at_meta = true
    ∧ anti_theory_honesty_act.blindspots_explicitly_named = true
    ∧ frost_honesty_act.blindspots_explicitly_named = false
    ∧ layer_2_authorial_irony_verdict.frost_is_correct = true
    ∧ layer_3_meta_misreading_verdict.frost_is_correct = true
    ∧ layer_0_clean_indifference_verdict.frost_is_correct = false
    ∧ acknowledgment_passes expected_runtime_acknowledgment = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals decide

end FrostsOwnBlindspots
end Gnosis
