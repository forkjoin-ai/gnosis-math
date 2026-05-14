import Gnosis.GodelIncompletenessShadow
import Gnosis.GodelUniverseIncompleteness
import Gnosis.NegativeKnowledgeAsState
import Gnosis.VoidIsBettiManifold

/-!
# Gnosis.IncompletenessBettiFrontier

This bridge packages the uncovered direction suggested by the
incompleteness and Betti-manifold work:

* bounded Goedel witnesses expose a real finite frontier;
* the Betti/void view says the frontier has residual unmeasured paths;
* negative-knowledge accounting says an unmeasured void must be promoted by
  measurement before it can count as a documented hole.

The module deliberately proves a frontier discipline, not a completion claim.
-/

namespace Gnosis
namespace IncompletenessBettiFrontier

/-- A bounded incompleteness witness records that a sentence and its negation
    are both absent from a finite proof budget. -/
structure BoundedIncompletenessWitness where
  budget : Nat
  sentence_unproved :
    _root_.GodelIncompletenessShadow.provableUpTo
      _root_.GodelIncompletenessShadow.pool
      budget
      _root_.GodelIncompletenessShadow.G = false
  negation_unproved :
    _root_.GodelIncompletenessShadow.provableUpTo
      _root_.GodelIncompletenessShadow.pool
      budget
      (_root_.GodelIncompletenessShadow.Form.neg _root_.GodelIncompletenessShadow.G)
      = false

/-- The canonical depth-4 Goedel shadow already proved in
    `GodelIncompletenessShadow`. -/
def goedelDepth4Witness : BoundedIncompletenessWitness :=
  { budget := 4
  , sentence_unproved :=
      _root_.GodelIncompletenessShadow.goedel_bounded_first_incompleteness.left
  , negation_unproved :=
      _root_.GodelIncompletenessShadow.goedel_bounded_first_incompleteness.right }

/-- A frontier is uncovered when a bounded proof wall, a Betti region, a
    residual void, and a ledger record all refer to an unmeasured boundary. -/
structure UncoveredFrontier where
  witness : BoundedIncompletenessWitness
  betti_region : VoidIsBettiManifold.BettiManifoldRegion
  void_region : VoidIsBettiManifold.VoidRegion
  ledger_record : NegativeKnowledgeAsState.KnowledgeRecord

/-- The session frontier: bounded Goedel gap, post-F5 Betti region, residual
    void, and the still-unmeasured Llama-1B ledger point. -/
def sessionFrontier : UncoveredFrontier :=
  { witness := goedelDepth4Witness
  , betti_region := VoidIsBettiManifold.session_unknot_region
  , void_region := VoidIsBettiManifold.session_void
  , ledger_record := NegativeKnowledgeAsState.llama_1b_record }

/-- A frontier is measurement-ready when its Betti and void views are dual,
    the void still has unmeasured paths, and the ledger record is a
    `NegativeUnknown`. -/
def measurementReady (f : UncoveredFrontier) : Prop :=
  VoidIsBettiManifold.regions_are_dual f.betti_region f.void_region = true
    ∧ f.void_region.unmeasured_path_count > 0
    ∧ f.ledger_record.state = NegativeKnowledgeAsState.KnowledgeState.NegativeUnknown

/-- The current session has an uncovered frontier: bounded incompleteness is
    witnessed at depth 4, the Betti and void views are dual, and the ledger
    still contains an unmeasured candidate. -/
theorem session_frontier_is_measurement_ready :
    measurementReady sessionFrontier := by
  unfold measurementReady sessionFrontier
  exact ⟨VoidIsBettiManifold.session_unknot_region_and_void_are_dual,
    VoidIsBettiManifold.the_runtime_is_surrounded_by_void,
    NegativeKnowledgeAsState.llama_1b_is_NegativeUnknown⟩

/-- The depth-4 Goedel frontier is exactly bounded: both the sentence and its
    negation are absent from the finite proof budget. -/
theorem session_frontier_has_bounded_goedel_gap :
    sessionFrontier.witness.sentence_unproved
      = _root_.GodelIncompletenessShadow.goedel_bounded_first_incompleteness.left
    ∧ sessionFrontier.witness.negation_unproved
      = _root_.GodelIncompletenessShadow.goedel_bounded_first_incompleteness.right := by
  exact ⟨rfl, rfl⟩

/-- The uncovered direction is information gain: a documented absence carries
    strictly more information than the same subject left as a negative unknown. -/
theorem documented_absence_dominates_uncovered_frontier
    (f : UncoveredFrontier) :
    NegativeKnowledgeAsState.information_content
      { subject := f.ledger_record.subject
      , state := NegativeKnowledgeAsState.KnowledgeState.PositiveAbsence
      , prior_state := f.ledger_record.prior_state
      , reason_for_transition := f.ledger_record.reason_for_transition }
    >
    NegativeKnowledgeAsState.information_content
      { subject := f.ledger_record.subject
      , state := NegativeKnowledgeAsState.KnowledgeState.NegativeUnknown
      , prior_state := none
      , reason_for_transition := "" } := by
  exact NegativeKnowledgeAsState.PositiveAbsence_dominates_NegativeUnknown
    f.ledger_record.subject
    f.ledger_record.prior_state
    f.ledger_record.reason_for_transition

/-- Bounded non-derivability is not a proof of absence. It can only be routed
    into the negative-knowledge ledger as a measurement-ready frontier. -/
theorem bounded_gap_points_to_measurement_not_completion :
    measurementReady sessionFrontier
      ∧ NegativeKnowledgeAsState.stateInformationContent
          NegativeKnowledgeAsState.KnowledgeState.NegativeUnknown
        < NegativeKnowledgeAsState.stateInformationContent
          NegativeKnowledgeAsState.KnowledgeState.PositiveAbsence := by
  exact ⟨session_frontier_is_measurement_ready,
    NegativeKnowledgeAsState.negative_unknown_carries_LESS_information_than_positive_absence⟩

/-- A structurally embedded observer with a valid model still leaves a positive
    model gap whenever it claims total coverage. This gives the same frontier
    shape as the session-level Betti/void witness. -/
theorem embedded_model_gap_blocks_omniscience
    {U O M : Nat}
    (h_embed : _root_.EmbeddedObserver_GodelUniverseIncompleteness U O)
    (h_valid : _root_.ValidModel O M) :
    M < U := by
  exact _root_.universal_incompleteness h_embed h_valid

end IncompletenessBettiFrontier
end Gnosis
