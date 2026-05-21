import Gnosis.AffectLabelingPatternInterrupt
import Gnosis.ConversationalProsody

namespace Gnosis
namespace AffectLabelingClosure

open Gnosis.ConversationalDodgeball
open Gnosis.ConversationalProsody
open Gnosis.AffectLabelingPatternInterrupt

/-- Fact question obligation carried through affect work. Affect labeling can
    make the next question/answer more disciplined, but it does not answer the
    fact question. -/
structure FactQuestionObligation where
  frame : QuestionFrame
  closure : ConversationClosure
  deriving Repr, DecidableEq

inductive DodgeballLoopExit where
  | stayInDodgeball
  | walkback
  | walkaway
  | arguedClosure
  deriving DecidableEq, Repr

def isOpenObligation (obligation : FactQuestionObligation) : Prop :=
  obligation.closure = .unresolved

/-- Only walkaway ends the conversation. Argued closure closes the fact
    topology while leaving room for the next conversational turn. Walkback
    revises the frame and keeps the obligation open. -/
def conversationEndedByExit : DodgeballLoopExit → Bool
  | .walkaway => true
  | .stayInDodgeball => false
  | .walkback => false
  | .arguedClosure => false

def applyAffectRouteToObligation
    (_route : AffectInterruptRoute)
    (obligation : FactQuestionObligation) : FactQuestionObligation :=
  { obligation with closure := .unresolved }

def closeObligationWithMove
    (obligation : FactQuestionObligation)
    (move : ConversationMove) : FactQuestionObligation :=
  { obligation with closure := closureOfMove move }

def closureOfAffectInterrupt
    (_trace : AffectInterruptTrace) : ConversationClosure :=
  .unresolved

/-- Walkaway records an explicit boundary exit, not an accidental bail-out. -/
def closureOfLoopExit : DodgeballLoopExit → ConversationClosure
  | .stayInDodgeball => .unresolved
  | .walkback => .unresolved
  | .walkaway => .boundaryRejected
  | .arguedClosure => .argued

def loopExitOfClosure : ConversationClosure → DodgeballLoopExit
  | .argued => .arguedClosure
  | .boundaryRejected => .walkaway
  | .silence => .stayInDodgeball
  | .bareTruth => .stayInDodgeball
  | .unresolved => .stayInDodgeball

def stayInDodgeballUntilExit
    (route : AffectInterruptRoute) (exit : DodgeballLoopExit)
    (obligation : FactQuestionObligation) : FactQuestionObligation :=
  match exit with
  | .stayInDodgeball => applyAffectRouteToObligation route obligation
  | .walkback => applyAffectRouteToObligation route obligation
  | .walkaway => { obligation with closure := .boundaryRejected }
  | .arguedClosure => { obligation with closure := .argued }

theorem affect_interrupt_closure_is_unresolved
    (trace : AffectInterruptTrace) :
    closureOfAffectInterrupt trace = .unresolved := by
  rfl

theorem affect_interrupt_is_not_fact_closure
    (trace : AffectInterruptTrace) :
    ¬ closureDiscipline (closureOfAffectInterrupt trace) := by
  exact no_unresolved_closure

theorem affect_route_preserves_open_obligation
    (route : AffectInterruptRoute) (obligation : FactQuestionObligation) :
    isOpenObligation (applyAffectRouteToObligation route obligation) := by
  rfl

theorem affect_route_cannot_discharge_argument_obligation
    (route : AffectInterruptRoute) (obligation : FactQuestionObligation) :
    ¬ closureDiscipline
      (applyAffectRouteToObligation route obligation).closure := by
  exact no_unresolved_closure

theorem validated_affect_interrupt_preserves_question_obligation
    {trace : AffectInterruptTrace} (_h : affectInterruptValidated trace)
    (obligation : FactQuestionObligation) :
    isOpenObligation
      (applyAffectRouteToObligation (affectInterruptRoute trace) obligation) := by
  exact affect_route_preserves_open_obligation
    (affectInterruptRoute trace) obligation

theorem stay_exit_keeps_open
    (route : AffectInterruptRoute) (obligation : FactQuestionObligation) :
    isOpenObligation
      (stayInDodgeballUntilExit route .stayInDodgeball obligation) := by
  exact affect_route_preserves_open_obligation route obligation

theorem walkback_exit_keeps_open
    (route : AffectInterruptRoute) (obligation : FactQuestionObligation) :
    isOpenObligation
      (stayInDodgeballUntilExit route .walkback obligation) := by
  exact affect_route_preserves_open_obligation route obligation

theorem walkaway_ends_conversation :
    conversationEndedByExit .walkaway = true := by
  rfl

theorem stay_keeps_conversation_open :
    conversationEndedByExit .stayInDodgeball = false := by
  rfl

theorem walkback_keeps_conversation_open :
    conversationEndedByExit .walkback = false := by
  rfl

theorem argued_closure_keeps_conversation_open :
    conversationEndedByExit .arguedClosure = false := by
  rfl

theorem walkaway_exit_is_boundary_rejection
    (route : AffectInterruptRoute) (obligation : FactQuestionObligation) :
    (stayInDodgeballUntilExit route .walkaway obligation).closure =
      .boundaryRejected := by
  rfl

theorem walkaway_exit_has_closure_discipline
    (route : AffectInterruptRoute) (obligation : FactQuestionObligation) :
    closureDiscipline
      (stayInDodgeballUntilExit route .walkaway obligation).closure := by
  exact boundary_rejection_has_discipline

theorem argued_exit_has_closure_discipline
    (route : AffectInterruptRoute) (obligation : FactQuestionObligation) :
    closureDiscipline
      (stayInDodgeballUntilExit route .arguedClosure obligation).closure := by
  exact argued_closure_has_discipline

theorem stay_exit_is_not_closure
    (route : AffectInterruptRoute) (obligation : FactQuestionObligation) :
    ¬ closureDiscipline
      (stayInDodgeballUntilExit route .stayInDodgeball obligation).closure := by
  exact no_unresolved_closure

theorem walkback_exit_is_not_closure
    (route : AffectInterruptRoute) (obligation : FactQuestionObligation) :
    ¬ closureDiscipline
      (stayInDodgeballUntilExit route .walkback obligation).closure := by
  exact no_unresolved_closure

theorem direct_answer_closes_after_affect_interrupt
    (route : AffectInterruptRoute) (obligation : FactQuestionObligation) :
    closureDiscipline
      (closeObligationWithMove
        (applyAffectRouteToObligation route obligation)
        .directAnswer).closure := by
  exact direct_answer_closes_with_discipline

theorem boundary_rejection_closes_after_affect_interrupt
    (route : AffectInterruptRoute) (obligation : FactQuestionObligation) :
    closureDiscipline
      (closeObligationWithMove
        (applyAffectRouteToObligation route obligation)
        (.tactic .dive)).closure := by
  exact boundary_rejection_has_discipline

theorem affect_interrupt_ready_routes_audit_gap
    (gate : ConversationalReynoldsGate)
    (signal : ConversationalProsodySignal)
    (trace : AffectInterruptTrace)
    (hReady : prosodyReadyToClose gate signal = true) :
    thothSemioticMove gate signal (closureOfAffectInterrupt trace) =
      .auditGap := by
  exact ready_undisciplined_routes_audit_gap gate signal .unresolved
    hReady rfl

theorem affect_interrupt_not_ready_routes_glossolalia
    (gate : ConversationalReynoldsGate)
    (signal : ConversationalProsodySignal)
    (trace : AffectInterruptTrace)
    (hReady : prosodyReadyToClose gate signal = false) :
    thothSemioticMove gate signal (closureOfAffectInterrupt trace) =
      .glossolaliaProbe := by
  exact not_ready_routes_glossolalia gate signal .unresolved hReady

theorem affect_interrupt_never_routes_closure_fold
    (gate : ConversationalReynoldsGate)
    (signal : ConversationalProsodySignal)
    (trace : AffectInterruptTrace) :
    thothSemioticMove gate signal (closureOfAffectInterrupt trace) ≠
      .closureFold := by
  cases hReady : prosodyReadyToClose gate signal with
  | false =>
      rw [affect_interrupt_not_ready_routes_glossolalia
        gate signal trace hReady]
      intro h
      cases h
  | true =>
      rw [affect_interrupt_ready_routes_audit_gap
        gate signal trace hReady]
      intro h
      cases h

theorem dodgeball_affect_interrupt_preserves_question_obligation
    {tactic : DodgeballTactic} {trace : AffectInterruptTrace}
    (h : dodgeballAffectInterruptValidates tactic trace)
    (obligation : FactQuestionObligation) :
    isOpenObligation
      (applyAffectRouteToObligation (affectInterruptRoute trace) obligation) := by
  exact validated_affect_interrupt_preserves_question_obligation h.2 obligation

theorem dodgeball_affect_interrupt_not_fact_closure
    {tactic : DodgeballTactic} {trace : AffectInterruptTrace}
    (_h : dodgeballAffectInterruptValidates tactic trace)
    (obligation : FactQuestionObligation) :
    ¬ closureDiscipline
      (applyAffectRouteToObligation
        (affectInterruptRoute trace) obligation).closure := by
  exact affect_route_cannot_discharge_argument_obligation
    (affectInterruptRoute trace) obligation

theorem no_bail_from_affect_stall
    (route : AffectInterruptRoute) (obligation : FactQuestionObligation) :
    loopExitOfClosure
      (stayInDodgeballUntilExit route .stayInDodgeball obligation).closure =
      .stayInDodgeball := by
  rfl

theorem no_bail_from_walkback
    (route : AffectInterruptRoute) (obligation : FactQuestionObligation) :
    loopExitOfClosure
      (stayInDodgeballUntilExit route .walkback obligation).closure =
      .stayInDodgeball := by
  rfl

theorem walkback_preserves_question_obligation
    (route : AffectInterruptRoute) (obligation : FactQuestionObligation) :
    isOpenObligation
      (stayInDodgeballUntilExit route .walkback obligation) ∧
    conversationEndedByExit .walkback = false := by
  exact ⟨walkback_exit_keeps_open route obligation, rfl⟩

theorem exits_are_walkaway_or_closure
    (route : AffectInterruptRoute) (obligation : FactQuestionObligation) :
    closureDiscipline
      (stayInDodgeballUntilExit route .walkaway obligation).closure ∧
    closureDiscipline
      (stayInDodgeballUntilExit route .arguedClosure obligation).closure := by
  exact ⟨walkaway_exit_has_closure_discipline route obligation,
    argued_exit_has_closure_discipline route obligation⟩

end AffectLabelingClosure
end Gnosis
