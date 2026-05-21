namespace Gnosis.Witnesses.Bible.Romans
namespace RomansIsraelMercyStumblingWitness

/-!
# Romans 9-11 -- Promise, Mercy, Stumblingstone, Remnant, and Olive Tree

Source slice: Romans 9:1-11:36.

Invariant: descent is not possession. Promise cuts through flesh-lineage,
mercy outruns willing and running, and the potter/clay image blocks the creature
from making itself auditor over the source. Gentile inclusion is not replacement
swagger; it is mercy routing through the place once called "not my people."

Counterproof: zeal without knowledge builds its own righteousness and then
stumbles over the offered stone. The olive tree is the anti-boast machine:
natural branches can be broken off, wild branches can be grafted contrary to
nature, and every branch is carried by the root rather than carrying it.

No `sorry`, no new `axiom`.
-/

structure PromiseMercyStone where
  promiseChildrenCountedForSeed : Bool := true
  mercyNotOfWillingOrRunning : Bool := true
  potterHasPowerOverClay : Bool := true
  notMyPeopleCalledChildren : Bool := true
  remnantSeedPreventsSodomPattern : Bool := true
  lawPursuitStumblesWithoutFaith : Bool := true
  confessionMouthHeartNearWord : Bool := true
  faithComesByHearing : Bool := true
deriving DecidableEq, Repr

def promiseMercyStone : PromiseMercyStone := {}

def mercyRoutesBeyondPossession (p : PromiseMercyStone) : Prop :=
  p.promiseChildrenCountedForSeed = true ∧
  p.mercyNotOfWillingOrRunning = true ∧
  p.potterHasPowerOverClay = true ∧
  p.notMyPeopleCalledChildren = true ∧
  p.remnantSeedPreventsSodomPattern = true ∧
  p.lawPursuitStumblesWithoutFaith = true ∧
  p.confessionMouthHeartNearWord = true ∧
  p.faithComesByHearing = true

structure RemnantOliveDoxology where
  godHasNotCastAwayForeknownPeople : Bool := true
  graceRemnantNotWorks : Bool := true
  fallBecomesGentileRiches : Bool := true
  wildBranchesGraftedContraryToNature : Bool := true
  boastAgainstBranchesRejected : Bool := true
  goodnessAndSeverityBothNamed : Bool := true
  giftsAndCallingWithoutRepentance : Bool := true
  allConcludedInUnbeliefForMercy : Bool := true
  judgmentsPastFindingOut : Bool := true
deriving DecidableEq, Repr

def remnantOliveDoxology : RemnantOliveDoxology := {}

def oliveTreeBreaksTribalBoasting (r : RemnantOliveDoxology) : Prop :=
  r.godHasNotCastAwayForeknownPeople = true ∧
  r.graceRemnantNotWorks = true ∧
  r.fallBecomesGentileRiches = true ∧
  r.wildBranchesGraftedContraryToNature = true ∧
  r.boastAgainstBranchesRejected = true ∧
  r.goodnessAndSeverityBothNamed = true ∧
  r.giftsAndCallingWithoutRepentance = true ∧
  r.allConcludedInUnbeliefForMercy = true ∧
  r.judgmentsPastFindingOut = true

theorem romans_mercy_routes_beyond_possession :
    mercyRoutesBeyondPossession promiseMercyStone := by
  unfold mercyRoutesBeyondPossession promiseMercyStone
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem romans_olive_tree_breaks_tribal_boasting :
    oliveTreeBreaksTribalBoasting remnantOliveDoxology := by
  unfold oliveTreeBreaksTribalBoasting remnantOliveDoxology
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem romans_israel_mercy_stumbling_witness :
    mercyRoutesBeyondPossession promiseMercyStone ∧
    oliveTreeBreaksTribalBoasting remnantOliveDoxology := by
  exact ⟨romans_mercy_routes_beyond_possession,
    romans_olive_tree_breaks_tribal_boasting⟩

end RomansIsraelMercyStumblingWitness
end Gnosis.Witnesses.Bible.Romans
