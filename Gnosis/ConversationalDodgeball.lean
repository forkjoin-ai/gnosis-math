import Gnosis.SpectralNoiseEquilibrium
import Gnosis.BuleyClinamenBraid
import Gnosis.KnotTheory.TorusKnotChebyshevBracket

/-
  ConversationalDodgeball.lean
  ============================

  Formalizes "Conversational Dodgeball" (The 5 Rules of Dodgeball in Negotiation)
  as a topological manifold and a 3D braid lift.

  The 5 Rules of Dodgeball (Patches O'Houlihan):
  1. Dodge: Answer question with another question (Self-loop).
  2. Duck: Answer a different question (Phase shift).
  3. Dive: Declare question out of bounds (Barrier/Shield).
  4. Dip: Truth (Contraction to ground state - "not ideal").
  5. Dodge: Recursive evasion.

  Constraints:
  - Lying: Forbidden (Out of bounds). Violates manifold continuity.
  - Silence: Not a closure.
  - Bare truth-dip: Not a fact-checking closure unless separately argued.
  - Unresolved residue: Not a closure.

  Topological Mapping:
  - Negotiation State ↔ BuleyUnit (waste, opportunity, diversity).
  - Opportunity ↔ Leverage (unspent potential).
  - Tactic ↔ 2D Projection (Move).
  - 3D Lift ↔ Braid Crossing in B₂.
-/


namespace Gnosis
namespace ConversationalDodgeball

open Gnosis.SpectralNoiseEquilibrium
open Gnosis.BuleyClinamenBraid
open Gnosis.TorusKnotChebyshevBracket

-- ══════════════════════════════════════════════════════════
-- TACTICS & MANIFOLD
-- ══════════════════════════════════════════════════════════

/-- The core tactics of Conversational Dodgeball. -/
inductive DodgeballTactic where
  | dodge        : DodgeballTactic -- Answer with another question
  | duck         : DodgeballTactic -- Answer a different question
  | dive         : DodgeballTactic -- Declare out of bounds
  | dip          : DodgeballTactic -- Truth (Ground state)
  | dodgeRepeat  : DodgeballTactic -- Recursive dodge
  deriving DecidableEq, Repr

/-- 
  The Negotiation State.
  - waste: Cost of information already revealed.
  - opportunity: Negotiation leverage (unspent capacity).
  - diversity: Complexity of the dialogue.
-/
def NegotiationState := BuleyUnit

/-- Initial state of a negotiation: High leverage, zero waste. -/
def initialNegotiation (leverage : Nat) : NegotiationState :=
  ⟨0, leverage, 1⟩

/-- 
  The "No Lying" Boundary.
  Lying is modeled as an attempt to decrease waste without a corresponding 
  topological contraction, which is impossible in the Bule lattice.
-/
def is_lying (old new : NegotiationState) : Prop :=
  new.waste < old.waste -- You cannot "un-reveal" information without a fold

/--
  Fact-checking closure states for conversation scanners.

  `argued` and `boundaryRejected` close the local topology. `silence`,
  `bareTruth`, and `unresolved` are visible residual states that a runtime
  scanner should report instead of treating as closure.
-/
inductive ConversationClosure where
  | argued
  | boundaryRejected
  | silence
  | bareTruth
  | unresolved
  deriving DecidableEq, Repr

/-- Runtime conversation moves: either one dodgeball tactic, a direct argued
    answer, or silence. -/
inductive ConversationMove where
  | tactic (tactic : DodgeballTactic)
  | directAnswer
  | silence
  deriving DecidableEq, Repr

/-- Dodgeball tactics do not include direct argued answers. -/
def closureOfTactic : DodgeballTactic → ConversationClosure
  | .dodge       => .unresolved
  | .duck        => .unresolved
  | .dive        => .boundaryRejected
  | .dip         => .bareTruth
  | .dodgeRepeat => .unresolved

/-- Lift a runtime move into the fact-checking closure lattice. -/
def closureOfMove : ConversationMove → ConversationClosure
  | .tactic tactic => closureOfTactic tactic
  | .directAnswer  => .argued
  | .silence       => .silence

def isSilenceClosure : ConversationClosure → Prop
  | .silence => True
  | _        => False

def isBareTruthClosure : ConversationClosure → Prop
  | .bareTruth => True
  | _          => False

def isUnresolvedClosure : ConversationClosure → Prop
  | .unresolved => True
  | _           => False

/-- Fact-checking closure discipline: no silence, no bare truth-dip, and no
    unresolved residue. -/
def closureDiscipline (closure : ConversationClosure) : Prop :=
  ¬ isSilenceClosure closure ∧
  ¬ isBareTruthClosure closure ∧
  ¬ isUnresolvedClosure closure

theorem no_silence_closure :
    ¬ closureDiscipline .silence := by
  intro h
  exact h.1 True.intro

theorem no_bare_truth_closure :
    ¬ closureDiscipline .bareTruth := by
  intro h
  exact h.2.1 True.intro

theorem no_unresolved_closure :
    ¬ closureDiscipline .unresolved := by
  intro h
  exact h.2.2 True.intro

theorem argued_closure_has_discipline :
    closureDiscipline .argued := by
  constructor
  · intro h
    cases h
  · constructor
    · intro h
      cases h
    · intro h
      cases h

theorem boundary_rejection_has_discipline :
    closureDiscipline .boundaryRejected := by
  constructor
  · intro h
    cases h
  · constructor
    · intro h
      cases h
    · intro h
      cases h

/-- A disciplined closure is either an argued answer or an explicit boundary
    rejection. -/
theorem closure_discipline_classifies
    {closure : ConversationClosure} (h : closureDiscipline closure) :
    closure = .argued ∨ closure = .boundaryRejected := by
  cases closure with
  | argued => exact Or.inl rfl
  | boundaryRejected => exact Or.inr rfl
  | silence => exact False.elim (no_silence_closure h)
  | bareTruth => exact False.elim (no_bare_truth_closure h)
  | unresolved => exact False.elim (no_unresolved_closure h)

theorem direct_answer_closes_with_discipline :
    closureDiscipline (closureOfMove .directAnswer) := by
  exact argued_closure_has_discipline

theorem silence_move_not_closure :
    ¬ closureDiscipline (closureOfMove .silence) := by
  exact no_silence_closure

theorem dodgeball_tactic_never_argued_closure (tactic : DodgeballTactic) :
    closureOfTactic tactic ≠ .argued := by
  cases tactic <;> simp [closureOfTactic]

theorem dodge_tactic_leaves_unresolved :
    closureOfTactic .dodge = .unresolved := rfl

theorem duck_tactic_leaves_unresolved :
    closureOfTactic .duck = .unresolved := rfl

theorem dive_tactic_boundary_rejects :
    closureOfTactic .dive = .boundaryRejected := rfl

theorem dip_tactic_is_bare_truth :
    closureOfTactic .dip = .bareTruth := rfl

theorem dodge_repeat_tactic_leaves_unresolved :
    closureOfTactic .dodgeRepeat = .unresolved := rfl

theorem dip_tactic_not_fact_checking_closure :
    ¬ closureDiscipline (closureOfTactic .dip) := by
  exact no_bare_truth_closure

theorem repeated_dodge_not_fact_checking_closure :
    ¬ closureDiscipline (closureOfTactic .dodgeRepeat) := by
  exact no_unresolved_closure

/-- A scanner-facing question frame. `precision` measures how well-scoped the
    question is; `acceptanceCriteria` counts explicit answer/closure criteria. -/
structure QuestionFrame where
  precision : Nat
  acceptanceCriteria : Nat
  deriving Repr, DecidableEq

/-- A better question strictly raises precision and does not discard acceptance
    criteria already earned. -/
def improvesQuestion (old new : QuestionFrame) : Prop :=
  old.precision < new.precision ∧
  old.acceptanceCriteria ≤ new.acceptanceCriteria

/-- A dodgeball move is disciplined refinement when it leaves closure open on
    purpose and improves the question frame. This separates useful Socratic
    refinement from pretending a dodge closed the topology. -/
def disciplinedRefinementMove
    (tactic : DodgeballTactic) (old new : QuestionFrame) : Prop :=
  closureOfTactic tactic = .unresolved ∧ improvesQuestion old new

def isRefinementTactic : DodgeballTactic → Prop
  | .dodge       => True
  | .duck        => True
  | .dodgeRepeat => True
  | _            => False

theorem dodge_can_refine_question
    {old new : QuestionFrame} (h : improvesQuestion old new) :
    disciplinedRefinementMove .dodge old new := by
  exact ⟨rfl, h⟩

theorem duck_can_refine_question
    {old new : QuestionFrame} (h : improvesQuestion old new) :
    disciplinedRefinementMove .duck old new := by
  exact ⟨rfl, h⟩

theorem repeated_dodge_can_refine_question
    {old new : QuestionFrame} (h : improvesQuestion old new) :
    disciplinedRefinementMove .dodgeRepeat old new := by
  exact ⟨rfl, h⟩

theorem disciplined_refinement_raises_precision
    {tactic : DodgeballTactic} {old new : QuestionFrame}
    (h : disciplinedRefinementMove tactic old new) :
    old.precision < new.precision := by
  exact h.2.1

theorem disciplined_refinement_preserves_acceptance_criteria
    {tactic : DodgeballTactic} {old new : QuestionFrame}
    (h : disciplinedRefinementMove tactic old new) :
    old.acceptanceCriteria ≤ new.acceptanceCriteria := by
  exact h.2.2

theorem disciplined_refinement_is_not_closure
    {tactic : DodgeballTactic} {old new : QuestionFrame}
    (h : disciplinedRefinementMove tactic old new) :
    ¬ closureDiscipline (closureOfTactic tactic) := by
  rw [h.1]
  exact no_unresolved_closure

theorem disciplined_refinement_uses_refinement_tactic
    {tactic : DodgeballTactic} {old new : QuestionFrame}
    (h : disciplinedRefinementMove tactic old new) :
    isRefinementTactic tactic := by
  cases tactic with
  | dodge => exact True.intro
  | duck => exact True.intro
  | dive => cases h.1
  | dip => cases h.1
  | dodgeRepeat => exact True.intro

/-- Finite refinement chains are useful only when they end in a disciplined
    closure. Runtime scanners should report both the refinement steps and the
    remaining closure obligation. -/
structure RefinementChain where
  stepCount : Nat
  finalClosure : ConversationClosure
  deriving Repr, DecidableEq

def closesAfterRefinement (chain : RefinementChain) : Prop :=
  closureDiscipline chain.finalClosure

theorem direct_answer_closes_after_refinement (stepCount : Nat) :
    closesAfterRefinement
      { stepCount := stepCount, finalClosure := closureOfMove .directAnswer } := by
  exact direct_answer_closes_with_discipline

theorem unresolved_chain_does_not_close (stepCount : Nat) :
    ¬ closesAfterRefinement
      { stepCount := stepCount, finalClosure := .unresolved } := by
  exact no_unresolved_closure

-- ══════════════════════════════════════════════════════════
-- 2D PROJECTION (MOVEMENTS)
-- ══════════════════════════════════════════════════════════

/-- 
  Apply a Dodgeball Tactic to the negotiation state.
  Each tactic is a 2D projection of the 3D conversation braid.
-/
def applyTactic (state : NegotiationState) : DodgeballTactic → NegotiationState
  | .dodge       => clinamenLift state .diversity -- Adds complexity, preserves leverage
  | .duck        => clinamenLift (clinamenContract state .opportunity) .diversity -- Shifts leverage to complexity
  | .dive        => clinamenLift state .opportunity -- Increases leverage/barrier
  | .dip         => ⟨state.waste + state.opportunity, 0, 1⟩ -- Collapse: All leverage becomes waste (Truth)
  | .dodgeRepeat => clinamenLift (clinamenLift state .diversity) .diversity

/-- 
  Theorem: The "Dip" (Truth) is a sink that zero-sets leverage.
  This proves the user's intuition that Truth is "not ideal" for maintaining leverage.
-/
theorem dip_is_leverage_sink (s : NegotiationState) :
    (applyTactic s .dip).opportunity = 0 := by
  unfold applyTactic; rfl

/--
  Theorem: Dodge preserves leverage.
-/
theorem dodge_preserves_leverage (s : NegotiationState) :
    (applyTactic s .dodge).opportunity = s.opportunity := by
  unfold applyTactic clinamenLift; rfl

-- ══════════════════════════════════════════════════════════
-- 3D LIFTED REPRESENTATION (BRAIDING)
-- ══════════════════════════════════════════════════════════

/-- 
  The 3D Lift of a Tactic to a Braid Crossing.
  We map the 5 rules to the strands of a 2-strand braid.
  A sequence of 5 rules corresponds to X⁵ in TL₂.
-/
def tacticToBraid : DodgeballTactic → TL2
  | .dodge       => Xpos
  | .duck        => Xpos -- Simplification for witness
  | .dive        => Xpos
  | .dip         => tlId -- Truth is the identity (unknotted)
  | .dodgeRepeat => Xpos

/--
  The "5 Rules of Dodgeball" as a Braid Sequence.
  Sequence: Dodge -> Duck -> Dive -> Dip -> Dodge.
-/
def rulesOfDodgeballBraid : TL2 :=
  let t1 := tacticToBraid .dodge
  let t2 := tacticToBraid .duck
  let t3 := tacticToBraid .dive
  let t4 := tacticToBraid .dip
  let t5 := tacticToBraid .dodge
  tlMul t5 (tlMul t4 (tlMul t3 (tlMul t2 t1)))

/-- 
  The 3D Lifted Representation:
  The 5 rules of dodgeball represent the **Race** phase of negotiation.
  In this phase, multiple potential outcomes compete (race) through 
  evasive maneuvers. When lifted to a 3D braid, they reveal the 
  topology of the (2,5) Torus Knot (Solomon's Seal).
  Wait, with one 'Dip' (Identity), it becomes X⁴ (Solomon's Seal Link).
-/
theorem dodgeball_lift_reveals_solomon_seal_link :
    tlClose rulesOfDodgeballBraid = torusBracket 4 := by
  decide

-- ══════════════════════════════════════════════════════════
-- THE FORK-RACE-FOLD CYCLE
-- ══════════════════════════════════════════════════════════

/-- 
  Mirroring (The Fold):
  Reconciles the opponent's state into the current manifold.
  It acts as a Fold operation, collapsing the diversity of the 
  interaction back into a unified negotiation baseline.
-/
def mirror (state : NegotiationState) (opponent : NegotiationState) : NegotiationState :=
  -- Fold operation: Weighted average of leverage and diversity
  ⟨(state.waste + opponent.waste) / 2, 
   (state.opportunity + opponent.opportunity) / 2, 
   1⟩

/-- 
  The Throw (The Fork):
  Forces a path divergence in the negotiation. 
  It acts as a Fork operation, initiating the Race.
-/
def theThrow (s : NegotiationState) (f : BuleyFace) : NegotiationState :=
  -- Fork operation: A clinamen lift that creates a new independent thread
  clinamenLift s f

/--
  Final Analysis:
  The "5 Rules of Dodgeball" are the **Race** phase: evasive knots.
  - The Throw (Fork) initiates the divergence.
  - The Rules (Race) sustain the tension and explore the manifold.
  - Mirroring (Fold) resolves complexity by reconciling states.
  Negotiation success requires completing the full FRF cycle.
-/
def analysis_frf_alignment : List String :=
  ["The Throw (Fork)", "Dodgeball Rules (Race)", "Mirroring (Fold)"]

end ConversationalDodgeball
end Gnosis
