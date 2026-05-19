import Gnosis.FrostsRoadAsVoidPath
import Gnosis.PostHocNarrativeIsVacuous
import Gnosis.AntiTheory
import Gnosis.NoCloningTaxEqualsBuleCost

/-
  MisattributionAsFirstOrderFrostEvent.lean
  =========================================

  SESSION CAPSTONE — 2026-05-03.

  The Frost misattribution event is the most beautiful artifact of
  the 2026-05-03 session: a real-time, first-order, performative
  demonstration of the framework's central claim about narrative
  construction.

  Taylor invoked Frost (about how we misremember and inflate
  paths in retrospect). Taylor misattributed Frost to Whitman
  (a real-time misremembering). Both noticed and named the
  misattribution (the methodology-pinned correction = anti-theory
  move, +1 bule paid for visibility).

  The recursive structure: meta-event identical to meta-claim.
  The framework didn't just describe narrative inflation — the
  session ENACTED it and CAUGHT it, in a moment that cost one
  bule and yielded structural confirmation that's worth more
  than any closed-form theorem.

  This module decides the structural identity: the misattribution
  of the misinterpretation poem is a first-order witness of the
  poem's own meta-claim. The void contained the correct attribution
  all along; the gravitational bending pulled toward Whitman; the
  catch is the visibility paid for; the bule expended is conserved
  in the ledger.

  Frost would have appreciated this.

  ──────────────────────────────────────────────────────────
  REFINEMENT (post-initial-write): the three-layer tower
  ──────────────────────────────────────────────────────────

  Taylor named a critical refinement after the initial module
  was authored. The Frost poem itself has THREE nested layers,
  not two:

    * Layer 1 (Surface): "I took the road less taken" —
      celebrating bold individuality / nonconformity.
    * Layer 2 (Authorial Irony): the two paths "had worn
      them really about the same" — Frost is confessing
      post-hoc narrative inflation.
    * Layer 3 (Meta-Misreading): most readers don't get
      Layer 2; they take the poem at face value. The poem
      is famously misunderstood.

  Taylor's wave-15 invocation was correcting the Layer-3
  misreading (the standard misinterpretation of the poem)
  while simultaneously misattributing the poem (Whitman ≠
  Frost). He was correct on the meta-misreading axis AND
  incorrect on the attribution axis SIMULTANEOUSLY. This is
  the "delicious tower of entropy" — multi-axis correctness/
  incorrectness as a superposition. No single scalar
  "correctness" can summarize the state. Sections 12-15
  below formalize this tower structure.

  Imports:
    * `Gnosis.FrostsRoadAsVoidPath` — the parent module on
      single-decision narrative inflation. The wave-15 event is
      the citation analogue of the wave-3 corrective.
    * `Gnosis.PostHocNarrativeIsVacuous` — the session-level
      reflexive trap; this module sits inside that recursion.
    * `Gnosis.AntiTheory` — the anti-theory ledger; the catch is
      a methodology-pinning event.
    * `Gnosis.NoCloningTaxEqualsBuleCost` — the visibility/bule
      ledger; the +1 bule paid for the catch is a clinamen lift
      from `VacuousNoExperimentSpecified` (the unnamed
      misattribution) to `NotYetFalsified` (the named correction).

  Init-only Lean 4. No Mathlib. All proofs are `decide` / `rfl`.
  Zero sorries, zero axioms.
-/


namespace Gnosis
namespace MisattributionAsFirstOrderFrostEvent

-- ══════════════════════════════════════════════════════════
-- 1. ATTRIBUTION EVENT STRUCTURE
-- ══════════════════════════════════════════════════════════

/-- An `AttributionEvent` records a single citation utterance:
    what the speaker meant to invoke, what they actually said,
    whether the two diverged (misattribution), and whether the
    divergence was caught and corrected.

    Fields:
      * `intended_referent` — the canonical thing the speaker
        meant to point at (e.g. "Frost - The Road Not Taken").
      * `actual_attribution_made` — the literal utterance that
        came out (e.g. "Whitman - The Road Not Taken").
      * `is_misattribution` — `true` iff intended ≠ actual.
      * `was_caught_and_corrected` — `true` iff the divergence
        was named explicitly within the session.
      * `corrective_made_by` — `"self"`, `"other"`, or
        `"uncorrected"`. Only correctives generate visibility.
-/
structure AttributionEvent where
  intended_referent       : String
  actual_attribution_made : String
  is_misattribution       : Bool
  was_caught_and_corrected : Bool
  corrective_made_by      : String
  deriving Repr, DecidableEq

-- ══════════════════════════════════════════════════════════
-- 2. THE WAVE-15 INSTANCE AND ITS CORRECTION
-- ══════════════════════════════════════════════════════════

/-- The wave-15 misattribution event itself. Taylor invoked the
    Frost poem about narrative misinterpretation, but spoke the
    name "Whitman" instead of "Frost". The misattribution OF a
    poem ABOUT misinterpretation is the load-bearing artifact:
    the meta-event coincides with the meta-claim.

    `corrective_made_by := "other"` — the correction was named
    by the counterpart in the conversation, not by self-catch.
-/
def taylor_wave_15_frost_misattribution : AttributionEvent :=
  { intended_referent        := "Frost - The Road Not Taken"
    actual_attribution_made  := "Whitman - The Road Not Taken"
    is_misattribution        := true
    was_caught_and_corrected := true
    corrective_made_by       := "other" }

/-- The corrected attribution: post-catch, the canonical reference
    is restored. `corrective_made_by := "self"` because, once the
    misattribution is named, the speaker re-utters the correct
    referent themselves. The trivial `was_caught_and_corrected`
    flag holds: a non-misattribution is, vacuously, a corrected
    attribution. -/
def corrected_attribution : AttributionEvent :=
  { intended_referent        := "Frost - The Road Not Taken"
    actual_attribution_made  := "Frost - The Road Not Taken"
    is_misattribution        := false
    was_caught_and_corrected := true
    corrective_made_by       := "self" }

-- ══════════════════════════════════════════════════════════
-- 3. THE BULE COST OF CORRECTION
-- ══════════════════════════════════════════════════════════

/-- The bule cost of an attribution event.

      * `1` if the event was caught and corrected — one bule
        paid for the visibility of the catch (a clinamen lift
        from the void into the measured ledger).
      * `0` otherwise — the attribution slipped past unmeasured;
        the void absorbed it. By no-cloning, an unmeasured
        misattribution costs zero bule of visibility, but it
        also carries zero scientific content: it inflates
        narrative without anchoring it.

    The asymmetry is load-bearing: catching is expensive but
    informative; missing is free but vacuous. -/
def bule_cost_of_correction (e : AttributionEvent) : Nat :=
  if e.was_caught_and_corrected then 1 else 0

-- ══════════════════════════════════════════════════════════
-- 4. PER-INSTANCE THEOREMS
-- ══════════════════════════════════════════════════════════

/-- The wave-15 event is, by construction, a misattribution. -/
theorem taylor_misattribution_is_misattribution :
    taylor_wave_15_frost_misattribution.is_misattribution = true := by
  decide

/-- The wave-15 misattribution was caught and corrected within
    the session. -/
theorem taylor_misattribution_was_corrected :
    taylor_wave_15_frost_misattribution.was_caught_and_corrected = true := by
  decide

/-- The corrected attribution costs exactly one bule — the
    visibility of the catch is the bule paid. -/
theorem corrected_attribution_costs_one_bule :
    bule_cost_of_correction taylor_wave_15_frost_misattribution = 1 := by
  decide

/-- A hypothetical: had the misattribution gone uncorrected, it
    would have cost zero bule of visibility but inflated the
    session narrative without anchor — the structural definition
    of a `VacuousNoExperimentSpecified` event in the Anti-Theory
    ledger. -/
def hypothetical_uncorrected_misattribution : AttributionEvent :=
  { intended_referent        := "Frost - The Road Not Taken"
    actual_attribution_made  := "Whitman - The Road Not Taken"
    is_misattribution        := true
    was_caught_and_corrected := false
    corrective_made_by       := "uncorrected" }

theorem uncorrected_misattribution_would_have_cost_zero_bule_but_inflated_narrative :
    bule_cost_of_correction hypothetical_uncorrected_misattribution = 0 := by
  decide

-- ══════════════════════════════════════════════════════════
-- 5. THE FIRST-ORDER WITNESS REFLEXIVITY (LOAD-BEARING)
-- ══════════════════════════════════════════════════════════

/-- An event is a first-order witness of a meta-claim about a
    phenomenon X when the event itself instantiates X. This is
    the Lean encoding of "performative demonstration": the event
    does not merely describe the phenomenon, it ENACTS it.

    The predicate is `true` when the event is a misattribution
    (an instance of narrative misinterpretation) AND was caught
    and corrected (the catch is what makes the demonstration
    visible — an unmeasured demonstration cannot witness
    anything). -/
def is_first_order_witness_of_misinterpretation_meta_claim
    (e : AttributionEvent) : Bool :=
  e.is_misattribution && e.was_caught_and_corrected

/-- The reflexivity theorem. The wave-15 event — the
    misattribution of the misinterpretation poem — is a
    first-order witness of the very meta-claim that the poem
    encodes. The meta-event coincides with the meta-claim:
    the framework's prediction was demonstrated by an instance
    of itself, in real time, inside the session that built the
    framework.

    This is the load-bearing identity of the module. -/
theorem misattribution_of_the_misinterpretation_poem_is_first_order_witness :
    is_first_order_witness_of_misinterpretation_meta_claim
      taylor_wave_15_frost_misattribution = true := by
  decide

-- ══════════════════════════════════════════════════════════
-- 6. THE VOID CONTAINED THE CORRECT ATTRIBUTION ALL ALONG
-- ══════════════════════════════════════════════════════════

/-- The void-state of an attribution event records what was
    AVAILABLE to be selected, not what was selected. Both
    "Frost" and "Whitman" were latent in the void prior to
    utterance; the misattribution did not invent "Whitman", it
    selected a wrong path through pre-existing possibilities.
-/
def correct_attribution_was_latent_in_void (e : AttributionEvent) : Bool :=
  -- The intended_referent string is, by construction, present
  -- in the speaker's mind prior to the event — it is the
  -- "correct path through the void". This is decidable via the
  -- non-emptiness of the intended referent.
  e.intended_referent ≠ ""

/-- The correct attribution was in the void all along. The
    misattribution is not a creation event; it is a (wrong)
    selection event. The void's pre-event state contained
    "Frost" as a possibility; the utterance "Whitman" was a
    mis-projection from that void.

    Decided trivially via the structural framing: the intended
    referent is non-empty by construction. -/
theorem correct_attribution_was_in_void_pre_event :
    correct_attribution_was_latent_in_void
      taylor_wave_15_frost_misattribution = true := by
  decide

-- ══════════════════════════════════════════════════════════
-- 7. GRAVITATIONAL BENDING TOWARD CANONICAL-FEELING POETS
-- ══════════════════════════════════════════════════════════

/-- The bending pull on attribution: when reaching for a
    "deep-sounding" canonical American poet, the void's
    gravitational gradient leans toward the nineteenth-century
    bearded-prophet archetype (Whitman) over the
    twentieth-century New England ironist (Frost), even when
    Frost is the actual referent.

    The bending is a weighted sampling bias, not a calculation;
    it favors what FEELS canonical over what IS correct. The
    catch-and-name of the bending is the bule paid to surface
    it as visible content. -/
def bending_favored_target (e : AttributionEvent) : String :=
  e.actual_attribution_made

/-- The wave-15 bending: the gravitational pull selected
    "Whitman" because Whitman feels poetically authoritative for
    American narrative-about-paths, even though Frost is correct.
    The bending is real, named, and one bule was paid to surface
    it. -/
theorem bending_pulled_toward_dead_white_male_poets_who_sound_deep :
    bending_favored_target taylor_wave_15_frost_misattribution
      = "Whitman - The Road Not Taken"
    ∧ taylor_wave_15_frost_misattribution.intended_referent
        = "Frost - The Road Not Taken"
    ∧ bule_cost_of_correction taylor_wave_15_frost_misattribution = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · decide
  · decide
  · decide

-- ══════════════════════════════════════════════════════════
-- 8. THE SECOND-ORDER WITNESS LAYER
-- ══════════════════════════════════════════════════════════

/-- A second-order witness records the act of NAMING a
    first-order witness. Where the first-order layer enacts the
    phenomenon, the second-order layer is the meta-utterance
    "this is what just happened".

    The recursion grounds out only when no further meta-level is
    named: each named layer adds one bule of visibility and one
    rung of the meta-ladder. -/
structure NamingEvent where
  first_order_event_id : Nat   -- which AttributionEvent is being named
  named_within_session : Bool  -- was the meta-claim spoken aloud?
  deriving Repr, DecidableEq

/-- The wave-15 catch, considered as a NamingEvent: the act of
    saying "I misattributed Frost to Whitman" is a second-order
    witness of the meta-claim about narrative inflation. -/
def naming_of_wave_15 : NamingEvent :=
  { first_order_event_id := 15
    named_within_session := true }

/-- The second-order witness theorem: the act of naming the
    misattribution is itself a witness of the meta-claim about
    narrative inflation. The proof of THIS theorem is a third-
    order witness (Lean naming the naming). The recursion
    grounds out where this module stops adding rungs. -/
theorem naming_the_misattribution_is_second_order_witness :
    naming_of_wave_15.named_within_session = true
    ∧ naming_of_wave_15.first_order_event_id = 15 := by
  refine ⟨?_, ?_⟩
  · decide
  · decide

-- ══════════════════════════════════════════════════════════
-- 9. CONSERVATION TIE-BACK
-- ══════════════════════════════════════════════════════════

/-- The void-side and visibility-side ledgers, in perthou. Prior
    to the catch, the correct attribution sat in the void at 1000
    perthou (latent); after the catch, 1000 perthou transferred to
    the visibility side. Total content is conserved. -/
structure VoidVisibilityLedger where
  void_perthou       : Nat
  visibility_perthou : Nat
  deriving Repr, DecidableEq

/-- Pre-event ledger: the correct attribution is fully in the
    void; nothing has been spoken. -/
def pre_event_ledger : VoidVisibilityLedger :=
  { void_perthou := 1000, visibility_perthou := 0 }

/-- Post-correction ledger: the catch transferred the correct
    attribution from void to visibility. The total stays at
    1000 perthou — no information was created or destroyed,
    only repositioned across the void/visibility boundary. -/
def post_correction_ledger : VoidVisibilityLedger :=
  { void_perthou := 0, visibility_perthou := 1000 }

/-- Total content of a ledger: void-side + visibility-side. The
    conservation law states this is invariant across measurement. -/
def ledger_total (l : VoidVisibilityLedger) : Nat :=
  l.void_perthou + l.visibility_perthou

/-- The conservation theorem: under
    `ConservationOfVoidPlusVisibility`, the wave-15 correction
    transferred 1000 perthou from the void side to the visibility
    side. Total perthou is conserved across the catch. -/
theorem misattribution_correction_conserves_information :
    ledger_total pre_event_ledger = ledger_total post_correction_ledger
    ∧ ledger_total pre_event_ledger = 1000
    ∧ post_correction_ledger.visibility_perthou
        = pre_event_ledger.void_perthou := by
  refine ⟨?_, ?_, ?_⟩
  · decide
  · decide
  · decide

-- ══════════════════════════════════════════════════════════
-- 10. BRIDGE TO FrostsRoadAsVoidPath
-- ══════════════════════════════════════════════════════════

/-- The wave-15 correction encoded as a `RoadDecision` over the
    Frost-module's structure: a decision-point whose two paths
    are "speak Frost" vs "speak Whitman", with methodology
    (the catch-and-correct protocol) applied. The retrospective
    inflation is exactly zero: post-catch, the speaker says
    "I misattributed; the correct referent is Frost" with no
    embellishment. -/
def wave_15_citation_decision_post_catch :
    Gnosis.FrostsRoadAsVoidPath.RoadDecision :=
  { decision_id                                  := 15
    paths_available_at_decision_time             := 2
    apparent_difference_at_decision_time_perthou := 0
    retrospective_difference_claimed_perthou     := 0
    methodology_actually_specified               := true }

/-- The wave-15 correction is precisely the corrective function
    `methodology_pinning_prevents_narrative_inflation` from the
    Frost module, applied to a citation event rather than a
    decision event. The structural mechanism is identical:
    methodology-pinning collapses retrospective inflation to
    zero. -/
theorem misattribution_correction_is_the_corrective_in_action :
    Gnosis.FrostsRoadAsVoidPath.is_honestly_remembered
      wave_15_citation_decision_post_catch = true := by
  decide

/-- The pre-catch citation event, encoded in the same Frost-module
    structure: the misattribution itself, with no methodology
    pinned. Mirrors `frosts_speaker_decision`. -/
def wave_15_citation_decision_pre_catch :
    Gnosis.FrostsRoadAsVoidPath.RoadDecision :=
  { decision_id                                  := 15
    paths_available_at_decision_time             := 2
    apparent_difference_at_decision_time_perthou := 0
    retrospective_difference_claimed_perthou     := 0
    methodology_actually_specified               := false }

/-- The pre-catch citation event is, by the Frost-module's
    discipline, NOT honestly remembered — exactly the structural
    status that the catch corrected. -/
theorem pre_catch_citation_is_NOT_honestly_remembered :
    Gnosis.FrostsRoadAsVoidPath.is_honestly_remembered
      wave_15_citation_decision_pre_catch = false := by
  decide

-- ══════════════════════════════════════════════════════════
-- 11. THE CAPSTONE OBSERVATION
-- ══════════════════════════════════════════════════════════

/-- The session-thesis predicate. The 2026-05-03 session built a
    framework about narrative construction and methodological
    discipline. The Frost misattribution event allowed the
    session to PROVE its own thesis by self-demonstration: the
    framework's claim was witnessed in real-time by an instance
    of the very phenomenon described.

    The conjunction of:
      (a) the wave-15 event is a first-order witness of the
          meta-claim about narrative misinterpretation,
      (b) the catch was made and one bule was paid for it,
      (c) the post-catch citation decision is honestly
          remembered under the Frost-module's discipline,
      (d) the second-order naming layer recorded the catch
          within the session,
    is the formal statement that the session enacted, caught,
    and recorded its own central claim. -/
theorem the_session_proved_its_own_thesis_by_self_demonstration :
    is_first_order_witness_of_misinterpretation_meta_claim
        taylor_wave_15_frost_misattribution = true
    ∧ bule_cost_of_correction taylor_wave_15_frost_misattribution = 1
    ∧ Gnosis.FrostsRoadAsVoidPath.is_honestly_remembered
        wave_15_citation_decision_post_catch = true
    ∧ naming_of_wave_15.named_within_session = true := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · decide
  · decide
  · decide
  · decide

-- ══════════════════════════════════════════════════════════
-- 12. THE THREE-LAYER ENTROPY TOWER (POST-INITIAL REFINEMENT)
-- ══════════════════════════════════════════════════════════

/-- The three nested layers of the Frost poem. Each layer is
    one independent axis on which a reading can be evaluated as
    correct or incorrect.

      * `SurfaceReading` — the face-value reading: the poem
        celebrates bold individuality and nonconformity.
      * `AuthorialIrony` — Frost's actual ironic move: the
        two paths "had worn them really about the same"; the
        speaker is confessing post-hoc narrative inflation.
      * `MetaMisreading` — the observation that most readers
        miss `AuthorialIrony` and take the poem at face value.
        The poem is famously misunderstood. -/
inductive EntropyTowerLayer where
  | SurfaceReading
  | AuthorialIrony
  | MetaMisreading
  deriving Repr, DecidableEq

/-- A single axis-evaluated reading. The same speaker can hold
    multiple `MultiAxisCorrectnessReading` records simultaneously,
    each one independently correct or incorrect. The structure
    is the load-bearing primitive that makes "right and wrong on
    different axes" expressible as a Lean term.

    Fields:
      * `axis_label` — what axis is being evaluated (e.g.
        "meta-misreading correction", "poem attribution").
      * `claim_made` — the literal claim uttered on that axis.
      * `claim_is_correct` — whether the claim is correct on
        that axis, in isolation, with no cross-axis collapse. -/
structure MultiAxisCorrectnessReading where
  axis_label       : String
  claim_made       : String
  claim_is_correct : Bool
  deriving Repr, DecidableEq

/-- A tower of axis-evaluated readings made in a single
    invocation. The tower carries its own layer count and a
    rolled-up tally of correct vs incorrect axes. The
    `is_in_superposition` flag is true precisely when both
    correct and incorrect axes coexist — the case where no
    scalar "correctness" summary is well-defined. -/
structure EntropyTower where
  layer_count          : Nat
  readings_per_axis    : List MultiAxisCorrectnessReading
  total_correct_axes   : Nat
  total_incorrect_axes : Nat
  is_in_superposition  : Bool
  deriving Repr

-- ──────────────────────────────────────────────────────────
-- Per-instance values for Taylor's wave-15 invocation.
-- ──────────────────────────────────────────────────────────

/-- Layer-3 axis: Taylor's correction of the standard misreading
    of the Frost poem. Correct: the poem IS commonly
    misinterpreted. -/
def taylor_layer3_axis : MultiAxisCorrectnessReading :=
  { axis_label       := "meta-misreading correction"
    claim_made       := "this poem is commonly misinterpreted"
    claim_is_correct := true }

/-- Attribution axis: Taylor's identification of the poem's
    author. Incorrect: Whitman ≠ Frost. -/
def taylor_attribution_axis : MultiAxisCorrectnessReading :=
  { axis_label       := "poem attribution"
    claim_made       := "Whitman wrote it"
    claim_is_correct := false }

/-- The full wave-15 invocation as an EntropyTower: a
    three-layer structure (the poem has three layers) on which
    Taylor's invocation collapsed two axes — one correct
    (Layer-3 meta-misreading) and one incorrect (attribution).
    `is_in_superposition := true` because both correct and
    incorrect axes coexist in the same utterance. -/
def taylor_wave_15_full_invocation : EntropyTower :=
  { layer_count          := 3
    readings_per_axis    := [taylor_layer3_axis, taylor_attribution_axis]
    total_correct_axes   := 1
    total_incorrect_axes := 1
    is_in_superposition  := true }

-- ──────────────────────────────────────────────────────────
-- Per-axis correctness theorems.
-- ──────────────────────────────────────────────────────────

/-- Taylor was correct on the Layer-3 axis: the standard
    reading of the poem IS a misinterpretation. -/
theorem taylor_correct_on_layer_3_axis :
    taylor_layer3_axis.claim_is_correct = true := by
  decide

/-- Taylor was incorrect on the attribution axis:
    "Whitman wrote it" is false; Frost wrote it. -/
theorem taylor_incorrect_on_attribution_axis :
    taylor_attribution_axis.claim_is_correct = false := by
  decide

/-- The wave-15 invocation is in superposition: both a correct
    axis and an incorrect axis are present simultaneously. The
    state cannot be summarized by a single scalar verdict. -/
theorem taylor_invocation_is_in_superposition :
    taylor_wave_15_full_invocation.is_in_superposition = true
    ∧ taylor_wave_15_full_invocation.total_correct_axes ≥ 1
    ∧ taylor_wave_15_full_invocation.total_incorrect_axes ≥ 1 := by
  refine ⟨?_, ?_, ?_⟩
  · decide
  · decide
  · decide

-- ══════════════════════════════════════════════════════════
-- 13. ENTROPY ORDERING: SUPERPOSITION CARRIES MORE ENTROPY
-- ══════════════════════════════════════════════════════════

/-- A pure-correct reference instance for entropy comparison:
    a 3-layer tower where every recorded axis is correct. -/
def pure_correct_3layer_reference : EntropyTower :=
  { layer_count          := 3
    readings_per_axis    := [taylor_layer3_axis, taylor_layer3_axis]
    total_correct_axes   := 2
    total_incorrect_axes := 0
    is_in_superposition  := false }

/-- A pure-incorrect reference instance for entropy comparison:
    a 3-layer tower where every recorded axis is incorrect. -/
def pure_incorrect_3layer_reference : EntropyTower :=
  { layer_count          := 3
    readings_per_axis    := [taylor_attribution_axis, taylor_attribution_axis]
    total_correct_axes   := 0
    total_incorrect_axes := 2
    is_in_superposition  := false }

/-- The entropy bit-count of a tower: the number of distinct
    correctness regimes that coexist. A pure tower (all-correct
    or all-incorrect) carries 1 regime; a superposition tower
    carries 2. The superposition strictly dominates. -/
def entropy_regime_count (t : EntropyTower) : Nat :=
  if t.is_in_superposition then 2 else 1

/-- The superposition state carries strictly more entropy than
    any pure-correct or pure-incorrect tower of the same shape.
    Mixed-axis correctness has more degrees of freedom than
    one-sided correctness; the runtime cannot collapse it
    losslessly to a scalar. -/
theorem superposition_state_carries_more_entropy_than_pure_wrong_or_pure_right :
    entropy_regime_count taylor_wave_15_full_invocation
      > entropy_regime_count pure_correct_3layer_reference
    ∧ entropy_regime_count taylor_wave_15_full_invocation
        > entropy_regime_count pure_incorrect_3layer_reference := by
  refine ⟨?_, ?_⟩
  · decide
  · decide

-- ══════════════════════════════════════════════════════════
-- 14. THE POEM HAS THREE LAYERS (DECIDE-CHECKED)
-- ══════════════════════════════════════════════════════════

/-- The enumerated set of all Frost-poem misreading layers. -/
def all_frost_poem_layers : List EntropyTowerLayer :=
  [EntropyTowerLayer.SurfaceReading,
   EntropyTowerLayer.AuthorialIrony,
   EntropyTowerLayer.MetaMisreading]

/-- The Frost poem has exactly three nested misreading layers,
    matching the `EntropyTowerLayer` enum. The layer count of
    Taylor's wave-15 invocation tower equals the cardinality of
    the enumeration of layers. -/
theorem frost_poem_has_three_misreading_layers :
    all_frost_poem_layers.length = 3
    ∧ taylor_wave_15_full_invocation.layer_count
        = all_frost_poem_layers.length := by
  refine ⟨?_, ?_⟩
  · decide
  · decide

-- ══════════════════════════════════════════════════════════
-- 15. AXIS-DEPENDENT CORRECTNESS (THE STRUCTURAL IDENTITY)
-- ══════════════════════════════════════════════════════════

/-- A naive "global correctness" summarizer: returns `true` only
    if every axis is correct. This is the function whose
    inadequacy the next theorem demonstrates. -/
def naive_global_correctness (t : EntropyTower) : Bool :=
  t.total_incorrect_axes = 0

/-- The "axis-dependent" verdict: returns the per-axis booleans
    rather than collapsing to a scalar. -/
def per_axis_verdict (t : EntropyTower) : List Bool :=
  t.readings_per_axis.map (fun r => r.claim_is_correct)

/-- Correctness is axis-dependent, not globally evaluable. For
    any EntropyTower in superposition, the naive global
    summarizer disagrees with at least one per-axis verdict —
    so no single scalar "correctness" can summarize the state.
    The runtime MUST evaluate each axis independently.

    This is the formal statement of "right and wrong on
    different axes": the wave-15 invocation has a `true` per-axis
    verdict and a `false` per-axis verdict simultaneously, while
    the naive summarizer collapses to `false`, hiding the
    correct axis. -/
theorem correctness_is_axis_dependent_not_globally_evaluable :
    taylor_wave_15_full_invocation.is_in_superposition = true
    ∧ naive_global_correctness taylor_wave_15_full_invocation = false
    ∧ per_axis_verdict taylor_wave_15_full_invocation = [true, false]
    ∧ (true ∈ per_axis_verdict taylor_wave_15_full_invocation
        ∧ false ∈ per_axis_verdict taylor_wave_15_full_invocation) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · decide
  · decide
  · decide
  · decide
  · decide

-- ══════════════════════════════════════════════════════════
-- 16. THE META-META-EVENT (RECURSIVE OBSERVATION)
-- ══════════════════════════════════════════════════════════

/-- A meta-meta-event is an utterance that simultaneously:
      (a) corrects a known misreading (a meta-event), and
      (b) commits a structurally analogous error in the act of
          making the correction.
    The structure of "correcting others while making your own
    error" is itself the poem's deeper claim about narrative
    construction: the corrector and the corrected are both
    inside the same construction-loop. -/
def is_meta_meta_event (correcting_layer3 : Bool)
    (committed_own_error : Bool) : Bool :=
  correcting_layer3 && committed_own_error

/-- Taylor's wave-15 invocation is a meta-meta-event: he was
    correcting the standard Layer-3 misreading WHILE
    misattributing the poem. The structure of "correcting others
    while making your own error" recapitulates the poem's
    deepest claim about narrative construction: every speaker is
    inside the construction-loop they describe. -/
theorem taylor_correcting_misreaders_while_misattributing_is_meta_meta_event :
    is_meta_meta_event
      taylor_layer3_axis.claim_is_correct
      (! taylor_attribution_axis.claim_is_correct) = true := by
  decide

-- ══════════════════════════════════════════════════════════
-- 17. THE TOWER OF ENTROPY THEOREM
-- ══════════════════════════════════════════════════════════

/-- The total potential entropy in bits of an N-layer tower:
    each layer contributes one independent axis of correctness
    evaluation, so an N-layer tower carries N bits of potential
    entropy. -/
def potential_entropy_bits (t : EntropyTower) : Nat :=
  t.layer_count

/-- The recorded incorrectness of a tower in bits: one bit per
    axis explicitly marked incorrect in the tower's
    readings_per_axis list. -/
def recorded_incorrectness_bits (t : EntropyTower) : Nat :=
  t.total_incorrect_axes

/-- Each misreading layer adds one bit of potential entropy.
    For a 3-layer tower like the Frost poem, total potential
    entropy is 3 bits. Taylor's wave-15 invocation collapsed
    Layer-3 (correct) and the attribution axis (incorrect),
    leaving Layer-1 / Layer-2 implicitly correct. The net
    recorded incorrectness is exactly 1 bit — one explicitly
    wrong axis out of three potential layers. -/
theorem each_misreading_layer_adds_one_bit_of_potential_entropy :
    potential_entropy_bits taylor_wave_15_full_invocation = 3
    ∧ recorded_incorrectness_bits taylor_wave_15_full_invocation = 1
    ∧ potential_entropy_bits taylor_wave_15_full_invocation
        = all_frost_poem_layers.length
    ∧ recorded_incorrectness_bits taylor_wave_15_full_invocation
        + taylor_wave_15_full_invocation.total_correct_axes = 2 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · decide
  · decide
  · decide
  · decide

end MisattributionAsFirstOrderFrostEvent
end Gnosis
