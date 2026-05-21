import Gnosis.AffectLabelingClosure
import Gnosis.PureExtendedNoiseTheorem

namespace Gnosis
namespace ConversationalProsodyClosure

open Gnosis.ConversationalDodgeball
open Gnosis.ConversationalProsody
open Gnosis.AffectLabelingPatternInterrupt
open Gnosis.AffectLabelingClosure

/-!
# Conversational Prosody Closure

Integrated scanner contract for conversational vacuum pressure.

The component files prove the pieces:
- `ConversationalProsody` defines finite vacuum pressure and Thoth routing.
- `AffectLabelingPatternInterrupt` defines stall backoff, silence budget,
  cringe vacuum, and grit continuance.
- `AffectLabelingClosure` proves affect work cannot discharge a fact question.

This file connects those pieces into the route shape the runtime scanner needs:
open questions stay open while pressure remains, degeneration increases stall
space and grit, walkback keeps the revised question open, and only walkaway or
argued closure exits with fact-checking discipline.
-/

/-- One scanner-facing snapshot of the integrated topology. -/
structure ConversationalProsodyClosureSnapshot where
  stream : VacuumPressureStream
  route : ThothSemioticMove
  loopExit : DodgeballLoopExit
  closure : ConversationClosure
  conversationEnded : Bool
  deriving Repr, DecidableEq

/-- Finite scanner states for the conversational Markov walk. This deterministic
    skeleton makes unresolved residue explicit as shadow instead of treating it
    as closure. -/
inductive ConversationalMarkovWalkState where
  | questionVacuum
  | answerDrain
  | affectStall
  | walkbackRevision
  | walkawayBoundary
  | arguedClosure
  | unresolvedShadow
  deriving Repr, DecidableEq

def markovWalkStateOfExit : DodgeballLoopExit → ConversationalMarkovWalkState
  | .stayInDodgeball => .unresolvedShadow
  | .walkback => .walkbackRevision
  | .walkaway => .walkawayBoundary
  | .arguedClosure => .arguedClosure

def markovWalkStateAbsorbing : ConversationalMarkovWalkState → Bool
  | .walkawayBoundary => true
  | .arguedClosure => true
  | _ => false

def markovWalkShadowResidual
    (snapshot : ConversationalProsodyClosureSnapshot) : Nat :=
  if snapshot.conversationEnded || closureDisciplinedBool snapshot.closure then
    0
  else
    snapshot.stream.residue + 1

/-- A silence-stall icebreaker reframes the unresolved vacuum at higher
    resolution. It is an evolution-by-reframing move, not a closure. -/
structure GnosisIcebreakerReframe where
  before : QuestionFrame
  after : QuestionFrame
  stallFailureCount : Nat
  sharedGainWitnesses : Nat
  deriving Repr, DecidableEq

def gnosisIcebreakerValid (frame : GnosisIcebreakerReframe) : Prop :=
  improvesQuestion frame.before frame.after ∧
  2 ≤ frame.stallFailureCount ∧
  3 ≤ frame.sharedGainWitnesses

def gnosisIcebreakerConductance
    (frame : GnosisIcebreakerReframe) : Nat :=
  frame.sharedGainWitnesses

def gnosisIcebreakerNoiseResolution : Nat :=
  Gnosis.PureExtendedNoise.white_noise

def snapshotAfterExit
    (gate : ConversationalReynoldsGate)
    (signal : ConversationalProsodySignal)
    (route : AffectInterruptRoute)
    (exit : DodgeballLoopExit)
    (obligation : FactQuestionObligation) :
    ConversationalProsodyClosureSnapshot :=
  let after := stayInDodgeballUntilExit route exit obligation
  { stream := vacuumPressureStreamOf signal
    route := thothSemioticMove gate signal after.closure
    loopExit := exit
    closure := after.closure
    conversationEnded := conversationEndedByExit exit }

theorem open_question_vacuum_stays_in_dodgeball
    (gate : ConversationalReynoldsGate)
    (signal : ConversationalProsodySignal)
    (route : AffectInterruptRoute)
    (obligation : FactQuestionObligation)
    (_hOpen : isOpenObligation obligation)
    (hNotReady : prosodyReadyToClose gate signal = false) :
    (vacuumPressureStreamOf signal).sourceVacuum = vacuumStream signal ∧
    (vacuumPressureStreamOf signal).conductance = drainageCapacity signal ∧
    (vacuumPressureStreamOf signal).residue = remainingVacuum signal ∧
    isOpenObligation
      (stayInDodgeballUntilExit route .stayInDodgeball obligation) ∧
    thothSemioticMove gate signal
      (stayInDodgeballUntilExit route .stayInDodgeball obligation).closure =
        .glossolaliaProbe ∧
    conversationEndedByExit .stayInDodgeball = false := by
  exact ⟨rfl, rfl, rfl,
    stay_exit_keeps_open route obligation,
    not_ready_routes_glossolalia gate signal
      (stayInDodgeballUntilExit route .stayInDodgeball obligation).closure
      hNotReady,
    rfl⟩

theorem walkback_keeps_vacuum_obligation_open
    (gate : ConversationalReynoldsGate)
    (signal : ConversationalProsodySignal)
    (route : AffectInterruptRoute)
    (obligation : FactQuestionObligation)
    (_hOpen : isOpenObligation obligation)
    (hNotReady : prosodyReadyToClose gate signal = false) :
    isOpenObligation
      (stayInDodgeballUntilExit route .walkback obligation) ∧
    thothSemioticMove gate signal
      (stayInDodgeballUntilExit route .walkback obligation).closure =
        .glossolaliaProbe ∧
    conversationEndedByExit .walkback = false := by
  exact ⟨walkback_exit_keeps_open route obligation,
    not_ready_routes_glossolalia gate signal
      (stayInDodgeballUntilExit route .walkback obligation).closure
      hNotReady,
    rfl⟩

theorem degenerating_affect_stall_integrates_backoff_and_grit
    {trace : AffectInterruptTrace}
    (state : StallBackoffState)
    (metric : GritMetric)
    (obligation : FactQuestionObligation)
    (hDegenerates : traceDegenerates trace) :
    isOpenObligation
      (applyAffectRouteToObligation (affectInterruptRoute trace) obligation) ∧
    responseSilenceBudget (applyStallBackoffOnFailure trace state) =
      2 * responseSilenceBudget state ∧
    continuanceInFaceOfFailure metric
      (applyGritOnStallFailure trace metric) := by
  exact ⟨affect_route_preserves_open_obligation
      (affectInterruptRoute trace) obligation,
    degenerating_trace_backoff_doubles_response_silence state hDegenerates,
    degenerating_trace_updates_grit_continuance metric hDegenerates⟩

theorem ready_walkaway_or_argued_exit_closes_with_discipline
    (gate : ConversationalReynoldsGate)
    (signal : ConversationalProsodySignal)
    (route : AffectInterruptRoute)
    (exit : DodgeballLoopExit)
    (obligation : FactQuestionObligation)
    (hReady : prosodyReadyToClose gate signal = true)
    (hExit : exit = .walkaway ∨ exit = .arguedClosure) :
    closureDiscipline
      (stayInDodgeballUntilExit route exit obligation).closure ∧
    thothSemioticMove gate signal
      (stayInDodgeballUntilExit route exit obligation).closure =
        .closureFold := by
  cases hExit with
  | inl hWalkaway =>
      subst exit
      exact ⟨walkaway_exit_has_closure_discipline route obligation,
        ready_disciplined_routes_closure_fold gate signal
          .boundaryRejected hReady rfl⟩
  | inr hArgued =>
      subst exit
      exact ⟨argued_exit_has_closure_discipline route obligation,
        ready_disciplined_routes_closure_fold gate signal .argued hReady rfl⟩

theorem full_conversational_prosody_mechanization_not_ready
    (gate : ConversationalReynoldsGate)
    (signal : ConversationalProsodySignal)
    (route : AffectInterruptRoute)
    (obligation : FactQuestionObligation)
    (_hOpen : isOpenObligation obligation)
    (hNotReady : prosodyReadyToClose gate signal = false) :
    (snapshotAfterExit gate signal route .stayInDodgeball obligation).route =
      .glossolaliaProbe ∧
    (snapshotAfterExit gate signal route .stayInDodgeball obligation).closure =
      .unresolved ∧
    (snapshotAfterExit gate signal route .stayInDodgeball obligation).conversationEnded =
      false ∧
    markovWalkStateOfExit .stayInDodgeball = .unresolvedShadow ∧
    markovWalkShadowResidual
      (snapshotAfterExit gate signal route .stayInDodgeball obligation) =
        (vacuumPressureStreamOf signal).residue + 1 ∧
    isOpenObligation
      (stayInDodgeballUntilExit route .stayInDodgeball obligation) := by
  exact ⟨
    by
      simp [snapshotAfterExit, stayInDodgeballUntilExit,
        applyAffectRouteToObligation, thothSemioticMove, hNotReady],
    by simp [snapshotAfterExit, stayInDodgeballUntilExit,
      applyAffectRouteToObligation],
    by simp [snapshotAfterExit, conversationEndedByExit],
    by rfl,
    by simp [markovWalkShadowResidual, snapshotAfterExit,
      conversationEndedByExit, stayInDodgeballUntilExit,
      applyAffectRouteToObligation, closureDisciplinedBool],
    by exact stay_exit_keeps_open route obligation⟩

theorem full_conversational_prosody_mechanization_ready_exit
    (gate : ConversationalReynoldsGate)
    (signal : ConversationalProsodySignal)
    (route : AffectInterruptRoute)
    (exit : DodgeballLoopExit)
    (obligation : FactQuestionObligation)
    (hReady : prosodyReadyToClose gate signal = true)
    (hExit : exit = .walkaway ∨ exit = .arguedClosure) :
    (snapshotAfterExit gate signal route exit obligation).route = .closureFold ∧
    markovWalkStateAbsorbing (markovWalkStateOfExit exit) = true ∧
    markovWalkShadowResidual
      (snapshotAfterExit gate signal route exit obligation) = 0 ∧
    closureDiscipline
      (snapshotAfterExit gate signal route exit obligation).closure := by
  cases hExit with
  | inl hWalkaway =>
      subst exit
      have h := ready_walkaway_or_argued_exit_closes_with_discipline
        gate signal route .walkaway obligation hReady (Or.inl rfl)
      exact ⟨h.2, rfl,
        by simp [markovWalkShadowResidual, snapshotAfterExit,
          conversationEndedByExit, stayInDodgeballUntilExit,
          closureDisciplinedBool],
        h.1⟩
  | inr hArgued =>
      subst exit
      have h := ready_walkaway_or_argued_exit_closes_with_discipline
        gate signal route .arguedClosure obligation hReady (Or.inr rfl)
      exact ⟨h.2, rfl,
        by simp [markovWalkShadowResidual, snapshotAfterExit,
          conversationEndedByExit, stayInDodgeballUntilExit,
          closureDisciplinedBool],
        h.1⟩

theorem walkback_markov_walk_is_revision_not_absorption :
    markovWalkStateOfExit .walkback = .walkbackRevision ∧
    markovWalkStateAbsorbing (markovWalkStateOfExit .walkback) = false := by
  exact ⟨rfl, rfl⟩

theorem gnosis_icebreaker_reframes_silence_without_closure
    {frame : GnosisIcebreakerReframe}
    (h : gnosisIcebreakerValid frame) :
    frame.before.precision < frame.after.precision ∧
    markovWalkStateAbsorbing .walkbackRevision = false ∧
    0 < gnosisIcebreakerConductance frame ∧
    gnosisIcebreakerNoiseResolution =
      Gnosis.PureExtendedNoise.white_noise := by
  exact ⟨h.1.1, rfl, Nat.lt_of_lt_of_le (by decide) h.2.2, rfl⟩

theorem gnosis_icebreaker_uses_white_noise_resolution :
    gnosisIcebreakerNoiseResolution = 4 := by
  exact Gnosis.PureExtendedNoise.white_noise_eq_four

end ConversationalProsodyClosure
end Gnosis
