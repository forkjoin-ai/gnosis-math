import Gnosis.MathFoundations
import Gnosis.BracketedSpace

/-!
# Gnosis.CausalDiamond

Formalization of the Causal Diamond as a spacetime bracket.

A Causal Diamond in the Gnosis kernel is defined by two events:
1. Birth (B): The past apex of the diamond.
2. Death (D): The future apex of the diamond.

An event E is inside the diamond iff:
- E is in the future light cone of B: distance(B, E) <= (E.time - B.time) * c
- E is in the past light cone of D: distance(E, D) <= (D.time - E.time) * c

In natural Gnostic units, c = 1 light-picolorenzo / picolorenzo.
The interval ds^2 = -dt^2 + dr^2 determines causal membership.
-/

namespace Gnosis
namespace CausalDiamond

open ForkRaceFoldMath
open BracketedSpace

/-- A point in a discrete 1+1D Spacetime grid. -/
structure Event where
  time : Int -- picolorenzos
  space : Int -- light-picolorenzos
  deriving DecidableEq, BEq, Repr

/-- 
  Spacetime interval ds^2 = dr^2 - dt^2.
  Using (dr^2 - dt^2) so that:
  - ds^2 < 0  => Timelike (Causally connected)
  - ds^2 = 0  => Lightlike (Horizon)
  - ds^2 > 0  => Spacelike (Elsewhere)
-/
def intervalSquared (e1 e2 : Event) : Int :=
  let dt := e2.time - e1.time
  let dr := e2.space - e1.space
  (dr * dr) - (dt * dt)

/-- An event is in the Future Light Cone of a reference event. -/
def inFutureLightCone (ref e : Event) : Bool :=
  decide (ref.time <= e.time ∧ intervalSquared ref e <= 0)

/-- An event is in the Past Light Cone of a reference event. -/
def inPastLightCone (ref e : Event) : Bool :=
  decide (e.time <= ref.time ∧ intervalSquared ref e <= 0)

/-- 
  The Causal Diamond: a region of spacetime bounded by causality.
-/
structure CausalDiamond where
  birth : Event
  death : Event
  -- Birth must strictly precede death.
  valid : inFutureLightCone birth death = true ∧ decide (birth.time < death.time)
  deriving Repr

/-- Checked constructor for runtime-lowered finite diamonds. -/
def ofChecked (birth death : Event) : Option CausalDiamond :=
  if h : inFutureLightCone birth death = true ∧ decide (birth.time < death.time) then
    some { birth, death, valid := h }
  else
    none

/-- Membership in the Causal Diamond. -/
def contains (cd : CausalDiamond) (e : Event) : Bool :=
  inFutureLightCone cd.birth e && inPastLightCone cd.death e

/-- 
  The "Time Width" of the diamond. 
  Equivalent to the refinement budget.
-/
def timeWidth (cd : CausalDiamond) : Nat :=
  Int.toNat (cd.death.time - cd.birth.time)

/-- 
  The "God Gap" of a Causal Diamond is its spatial width at the midpoint.
  At the widest point, the spatial uncertainty is exactly the time width.
-/
def spatialWidth (cd : CausalDiamond) : Nat :=
  timeWidth cd

/-! ## Spacetime Refinement Tower -/

/-- 
  A sequence of diamonds that narrow around a specific spacetime event.
-/
structure CausalTower where
  step : Nat → CausalDiamond
  -- Refinement: cd_{n+1} is strictly inside cd_n
  refines : ∀ n e, contains (step (n+1)) e = true → contains (step n) e = true
  -- The God Gap shrinks as the tower ascends.
  shrinks : ∀ n, timeWidth (step (n+1)) < timeWidth (step n)

/-! ## The "Sliver" in Spacetime -/

/-- 
  A diamond with timeWidth 1 is a Spacetime Sliver.
  It is the fundamental unit of irreducible uncertainty in the Mesh.
-/
def isSliver (cd : CausalDiamond) : Bool :=
  decide (timeWidth cd ≤ 1)

/-! ## The Five Forces of Spacetime -/

/-- 
  FORK: Splits a causal diamond into two overlapping sub-diamonds.
  Used to parallelize the search for an event.
-/
def fork (cd : CausalDiamond) : CausalDiamond × CausalDiamond :=
  let midTime := (cd.birth.time + cd.death.time) / 2
  let mid := { time := midTime, space := cd.birth.space }
  match ofChecked cd.birth mid, ofChecked mid cd.death with
  | some d1, some d2 => (d1, d2)
  | _, _ => (cd, cd)

/-- 
  FOLD: The intersection of two causal diamonds.
  This is the geometric basis for Reynolds BFT Consensus.
-/
def fold (cd1 cd2 : CausalDiamond) : Option CausalDiamond :=
  -- Simplified 1+1D FOLD: 
  -- Birth = max(b1, b2) in causal order
  -- Death = min(d1, d2) in causal order
  if inFutureLightCone cd1.birth cd2.birth then
    if inPastLightCone cd1.death cd2.death then
      some cd2 -- cd2 is contained in cd1
    else
      none -- partial overlap not yet implemented
  else
    none

/-- 
  VENT: Discards a diamond that has been falsified or is acausal.
  In Gnosis, VENT represents the expulsion of noise from the system.
-/
def vent (_cd : CausalDiamond) : Bool :=
  false

/-- 
  RACE: Two diamonds competing to reach the SLIVER threshold.
  Returns the one that has narrower temporal width.
-/
def race (cd1 cd2 : CausalDiamond) : CausalDiamond :=
  if timeWidth cd1 <= timeWidth cd2 then cd1 else cd2

/-- 
  SLIVER: The terminal state of refinement.
  No further FOLDING is possible beyond this limit.
-/
def sliver_limit : Nat := 1

/-! ## Finite Runtime Certificates -/

def runtimeOuterDiamond : CausalDiamond :=
  { birth := { time := 0, space := 0 }
  , death := { time := 8, space := 0 }
  , valid := by native_decide }

def runtimeInnerDiamond : CausalDiamond :=
  { birth := { time := 2, space := 0 }
  , death := { time := 5, space := 0 }
  , valid := by native_decide }

def runtimeSliverDiamond : CausalDiamond :=
  { birth := { time := 4, space := 0 }
  , death := { time := 5, space := 0 }
  , valid := by native_decide }

/-- Checked candidate row: an event inside the inner diamond is also inside the outer one. -/
theorem runtime_inner_event_stays_in_outer :
    contains runtimeInnerDiamond { time := 3, space := 0 } = true
    ∧ contains runtimeOuterDiamond { time := 3, space := 0 } = true := by
  native_decide

/-- FOIL lowering certificate: race chooses the narrower non-sliver diamond first. -/
theorem runtime_race_prefers_inner_non_sliver :
    timeWidth runtimeOuterDiamond = 8
    ∧ timeWidth runtimeInnerDiamond = 3
    ∧ isSliver runtimeInnerDiamond = false
    ∧ timeWidth (race runtimeOuterDiamond runtimeInnerDiamond) = 3 := by
  native_decide

/-- FOIL lowering certificate: sliver diamonds terminate refinement. -/
theorem runtime_sliver_terminates_refinement :
    timeWidth runtimeSliverDiamond = sliver_limit
    ∧ isSliver runtimeSliverDiamond = true := by
  native_decide

/-- 
  THM-CONSENSUS-IS-CONTRACTION
  The width of a consensus diamond (FOLD) is bounded by its parents.
  Finite certificate for the FOIL lowering layer.
-/
def runtimeConsensusContractionCheck : Bool :=
  match fold runtimeOuterDiamond runtimeInnerDiamond with
  | some res => timeWidth res ≤ timeWidth runtimeOuterDiamond ∧ timeWidth res ≤ timeWidth runtimeInnerDiamond
  | none => false

theorem runtime_consensus_is_contraction :
    runtimeConsensusContractionCheck = true := by
  native_decide

/--
  THM-VENT-IS-ZERO-CONSENSUS
  If two diamonds are causally incompatible (one birth not in future of other), 
  their FOLD is 'none' in the current 1+1D implementation.
-/
def runtimeVentCheck : Bool :=
  let cd1 := runtimeOuterDiamond
  let cd2 : CausalDiamond := { birth := { time := 0, space := 5 }, death := { time := 10, space := 5 }, valid := by native_decide }
  match fold cd1 cd2 with
  | none => true
  | some _ => false

theorem runtime_vent_is_zero_consensus :
    runtimeVentCheck = true := by
  native_decide

/-! ## Promotion Obligations -/

structure SpacetimePromotionObligation where
  fullRefinement : Prop
  fullContraction : Prop
  fullVent : Prop

def spacetimePromotionObligation : SpacetimePromotionObligation :=
  { fullRefinement := ∀ cd1 cd2 e, contains cd2 e = true → contains cd1 e = true -- if cd2 inside cd1
  , fullContraction := ∀ cd1 cd2 res, fold cd1 cd2 = some res →
      timeWidth res ≤ timeWidth cd1 ∧ timeWidth res ≤ timeWidth cd2
  , fullVent := ∀ cd1 cd2, intervalSquared cd1.birth cd2.birth > 0 →
      fold cd1 cd2 = none }

end CausalDiamond
end Gnosis
