namespace Gnosis
namespace ThothConversationAntiQueue

/-!
# Thoth Conversation AntiQueue

This module formalizes the conversation task/todo antiqueue as an internal
self-accountability surface. It is not an external enforcement queue. A held
item records a promise Thoth makes to itself: keep an open question visible,
argue a closure diff, honor a stated boundary, or continue an affect stall until
the loop is explicitly closed, walked back, or walked away from.

No `sorry`, no new `axiom`.
-/

inductive AntiQueueItemKind where
  | openQuestion
  | argumentObligation
  | selfBoundary
  | affectStall
  | unresolvedResidue
deriving DecidableEq, Repr

inductive AntiQueueRelease where
  | arguedClosure
  | disciplinedWalkback
  | explicitWalkaway
  | selfBoundaryHonored
deriving DecidableEq, Repr

inductive ConversationLoopExit where
  | stayInDodgeball
  | walkback
  | walkaway
  | arguedClosure
deriving DecidableEq, Repr

structure ConversationAntiQueueState where
  openQuestions : Nat := 0
  argumentObligations : Nat := 0
  selfBoundaryPromises : Nat := 0
  affectStalls : Nat := 0
  unresolvedResidue : Nat := 0
  externallyAccountable : Bool := false
deriving DecidableEq, Repr

def antiQueueItemCount (s : ConversationAntiQueueState) : Nat :=
  s.openQuestions +
  s.argumentObligations +
  s.selfBoundaryPromises +
  s.affectStalls +
  s.unresolvedResidue

def antiQueuePressure (s : ConversationAntiQueueState) : Nat :=
  s.openQuestions * 5 +
  s.argumentObligations * 7 +
  s.selfBoundaryPromises * 6 +
  s.affectStalls * 4 +
  s.unresolvedResidue * 3

def selfAccountabilityOnly (s : ConversationAntiQueueState) : Prop :=
  s.externallyAccountable = false

def heldOpen (s : ConversationAntiQueueState) : Prop :=
  selfAccountabilityOnly s ∧ antiQueueItemCount s > 0

def releasableBy (s : ConversationAntiQueueState) (r : AntiQueueRelease) : Prop :=
  selfAccountabilityOnly s ∧
  match r with
  | AntiQueueRelease.arguedClosure =>
      s.argumentObligations = 0 ∧ s.unresolvedResidue = 0
  | AntiQueueRelease.disciplinedWalkback =>
      s.openQuestions > 0
  | AntiQueueRelease.explicitWalkaway =>
      s.openQuestions = 0 ∧ s.selfBoundaryPromises = 0
  | AntiQueueRelease.selfBoundaryHonored =>
      s.selfBoundaryPromises = 0

def releaseCompatible (k : AntiQueueItemKind) (r : AntiQueueRelease) : Prop :=
  match k, r with
  | AntiQueueItemKind.openQuestion, AntiQueueRelease.arguedClosure => True
  | AntiQueueItemKind.openQuestion, AntiQueueRelease.disciplinedWalkback => True
  | AntiQueueItemKind.openQuestion, AntiQueueRelease.explicitWalkaway => True
  | AntiQueueItemKind.argumentObligation, AntiQueueRelease.arguedClosure => True
  | AntiQueueItemKind.selfBoundary, AntiQueueRelease.explicitWalkaway => True
  | AntiQueueItemKind.selfBoundary, AntiQueueRelease.selfBoundaryHonored => True
  | AntiQueueItemKind.affectStall, AntiQueueRelease.arguedClosure => True
  | AntiQueueItemKind.affectStall, AntiQueueRelease.disciplinedWalkback => True
  | AntiQueueItemKind.affectStall, AntiQueueRelease.explicitWalkaway => True
  | AntiQueueItemKind.unresolvedResidue, AntiQueueRelease.arguedClosure => True
  | AntiQueueItemKind.unresolvedResidue, AntiQueueRelease.disciplinedWalkback => True
  | AntiQueueItemKind.unresolvedResidue, AntiQueueRelease.explicitWalkaway => True
  | AntiQueueItemKind.unresolvedResidue, AntiQueueRelease.selfBoundaryHonored => True
  | _, _ => False

def releaseForLoopExit : ConversationLoopExit → AntiQueueRelease
  | ConversationLoopExit.stayInDodgeball => AntiQueueRelease.arguedClosure
  | ConversationLoopExit.walkback => AntiQueueRelease.disciplinedWalkback
  | ConversationLoopExit.walkaway => AntiQueueRelease.explicitWalkaway
  | ConversationLoopExit.arguedClosure => AntiQueueRelease.arguedClosure

structure RuntimeDischarge where
  itemKind : AntiQueueItemKind
  release : AntiQueueRelease
  closureDischargeId : String
  argumentObligationIds : List String := []
  selfAccountabilityOnly : Bool := true
deriving DecidableEq, Repr

def runtimeDischargeSound (d : RuntimeDischarge) : Prop :=
  d.selfAccountabilityOnly = true ∧ releaseCompatible d.itemKind d.release

def kindPressure : AntiQueueItemKind → Nat
  | AntiQueueItemKind.openQuestion => 5
  | AntiQueueItemKind.argumentObligation => 7
  | AntiQueueItemKind.selfBoundary => 6
  | AntiQueueItemKind.affectStall => 4
  | AntiQueueItemKind.unresolvedResidue => 3

def nextTaskPressure (s : ConversationAntiQueueState) : Nat :=
  if s.selfBoundaryPromises > 0 then kindPressure AntiQueueItemKind.selfBoundary
  else if s.argumentObligations > 0 then kindPressure AntiQueueItemKind.argumentObligation
  else if s.unresolvedResidue > 0 then kindPressure AntiQueueItemKind.unresolvedResidue
  else if s.openQuestions > 0 then kindPressure AntiQueueItemKind.openQuestion
  else if s.affectStalls > 0 then kindPressure AntiQueueItemKind.affectStall
  else 0

def witnessState : ConversationAntiQueueState where
  openQuestions := 1
  argumentObligations := 1
  selfBoundaryPromises := 1
  affectStalls := 1
  unresolvedResidue := 1
  externallyAccountable := false

theorem witness_self_accountability :
    selfAccountabilityOnly witnessState := by
  unfold selfAccountabilityOnly witnessState
  rfl

theorem witness_held_open :
    heldOpen witnessState := by
  unfold heldOpen antiQueueItemCount selfAccountabilityOnly witnessState
  exact ⟨rfl, by decide⟩

theorem witness_positive_pressure :
    antiQueuePressure witnessState > 0 := by
  unfold antiQueuePressure witnessState
  decide

theorem release_never_requires_external_accountability
    (s : ConversationAntiQueueState)
    (r : AntiQueueRelease) :
    releasableBy s r → selfAccountabilityOnly s := by
  intro h
  unfold releasableBy at h
  exact h.left

theorem compatible_release_preserves_self_accountability
    (s : ConversationAntiQueueState)
    (k : AntiQueueItemKind)
    (r : AntiQueueRelease) :
    selfAccountabilityOnly s →
    releaseCompatible k r →
    selfAccountabilityOnly s := by
  intro h _
  exact h

theorem runtime_discharge_preserves_self_accountability
    (d : RuntimeDischarge) :
    runtimeDischargeSound d → d.selfAccountabilityOnly = true := by
  intro h
  exact h.left

theorem loop_exit_release_compatible_for_open_question
    (exit : ConversationLoopExit) :
    releaseCompatible AntiQueueItemKind.openQuestion (releaseForLoopExit exit) := by
  cases exit <;> unfold releaseForLoopExit releaseCompatible <;> trivial

theorem walkaway_open_question_runtime_discharge_sound
    (closureDischargeId : String) :
    runtimeDischargeSound
      { itemKind := AntiQueueItemKind.openQuestion
        release := AntiQueueRelease.explicitWalkaway
        closureDischargeId := closureDischargeId
        argumentObligationIds := []
        selfAccountabilityOnly := true } := by
  unfold runtimeDischargeSound releaseCompatible
  exact ⟨rfl, trivial⟩

theorem argued_closure_argument_obligation_runtime_discharge_sound
    (closureDischargeId : String)
    (argumentObligationIds : List String) :
    runtimeDischargeSound
      { itemKind := AntiQueueItemKind.argumentObligation
        release := AntiQueueRelease.arguedClosure
        closureDischargeId := closureDischargeId
        argumentObligationIds := argumentObligationIds
        selfAccountabilityOnly := true } := by
  unfold runtimeDischargeSound releaseCompatible
  exact ⟨rfl, trivial⟩

theorem self_boundary_not_released_by_argued_closure :
    ¬ releaseCompatible AntiQueueItemKind.selfBoundary AntiQueueRelease.arguedClosure := by
  intro h
  exact h

theorem witness_next_task_pressure_positive :
    nextTaskPressure witnessState > 0 := by
  unfold nextTaskPressure witnessState kindPressure
  decide

theorem empty_self_antiqueue_not_held :
    ¬ heldOpen ({ externallyAccountable := false } : ConversationAntiQueueState) := by
  intro h
  unfold heldOpen antiQueueItemCount selfAccountabilityOnly at h
  exact Nat.not_succ_le_zero 0 h.right

end ThothConversationAntiQueue
end Gnosis
