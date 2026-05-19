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
