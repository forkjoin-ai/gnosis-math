import Gnosis.Bridges.HumorTensegrityQueueKernelBridge
import Gnosis.AffectLabelingPatternInterrupt

/-!
# Topologist Joke Witness

Finite witness for our cafe version of the old joke:

> A topologist is sitting in a cafe with a pupil. The wry student, knowing the
> trope, asks: "Can you tell me the difference between this coffee mug and that
> donut on your plate?"
>
> The topologist picks up the mug, traces the handle, then points to the hole in
> the center of the donut. With a serene expression, he says: "To me, Betty,
> there is no difference. Both are genus-one surfaces. They are topologically
> identical."
>
> The student, maintaining her aplomb and wanting to score points, picks up a
> knife and asks: "Alright, if you can't tell the difference, should I butter
> your coffee mug?"
>
> The topologist pauses. The topological collapse — the ability to see them as
> the same — suddenly snaps back into the reality of the breakfast table. He
> pulls the mug away: "That would be a mistake. The mug holds coffee; the donut
> holds butter. One is a container; the other is breakfast."
>
> He adds: "My head is a genus-zero object, and that hole in the ground outside
> is a genus-one object, but I assure you, neither needs such buttering up."

The punchline is not "topologists cannot distinguish anything." It is that the
first comparison intentionally uses a coarse invariant, while the second forces
semantic snapback: container affordance, breakfast affordance, agency,
embodiment, and grounded absence are not erased by the handle-count joke.

The point is deliberately small: topological equivalence is not total
indistinguishability.
-/

namespace Gnosis
namespace TopologistJokeWitness

/-- Toy object classes used by the joke. -/
inductive JokeObject where
  | donut
  | coffeeMug
  | coffee
  | butter
  | emptyMug
  | beerGlass
  | barHandle
  | knife
  | proof
  | head
  | groundHole
  | keys
  | room
deriving DecidableEq

/-- Mechanisms already visible in the natural-language jokes. -/
inductive HumorMechanism where
  | topologicalCollapse
  | semanticSnapback
  | boundaryCondition
  | homotopyDeflection
  | cringeLeak
deriving DecidableEq

/-- The coarse topological handle count visible to the joke. -/
def genus : JokeObject → Nat
  | .donut => 1
  | .coffeeMug => 1
  | .coffee => 0
  | .butter => 0
  | .emptyMug => 1
  | .beerGlass => 0
  | .barHandle => 1
  | .knife => 0
  | .proof => 0
  | .head => 0
  | .groundHole => 1
  | .keys => 0
  | .room => 0

/-- A non-topological field: whether the object is a living occupant. -/
def hasAgency : JokeObject → Bool
  | .head => true
  | _ => false

/-- A non-topological field: whether the object is an absence in the ground. -/
def isGroundAbsence : JokeObject → Bool
  | .groundHole => true
  | _ => false

/-- A non-topological field: whether the object is drinkable. -/
def isDrinkable : JokeObject → Bool
  | .coffee => true
  | _ => false

/-- A breakfast-table affordance: whether butter belongs on the object. -/
def acceptsButter : JokeObject → Bool
  | .donut => true
  | _ => false

/-- A non-topological field: whether the object can hold a drink. -/
def canHoldDrink : JokeObject → Bool
  | .coffeeMug => true
  | .emptyMug => true
  | .beerGlass => true
  | _ => false

/-- A non-topological field: whether the object is a cutting implement. -/
def isWeaponLike : JokeObject → Bool
  | .knife => true
  | _ => false

/-- A semantic role for how an object appears in the joke. -/
inductive JokeRole where
  | breakfast
  | container
  | absence
  | body
  | tool
  | argument
  | location
deriving DecidableEq

/-- Semantic classification that topology alone forgets. -/
def semanticRole : JokeObject → JokeRole
  | .donut => .breakfast
  | .coffeeMug => .container
  | .coffee => .breakfast
  | .butter => .breakfast
  | .emptyMug => .container
  | .beerGlass => .container
  | .barHandle => .tool
  | .knife => .tool
  | .proof => .argument
  | .head => .body
  | .groundHole => .absence
  | .keys => .tool
  | .room => .location

/-- Coarse joke-topological equivalence: same genus only. -/
def jokeTopologicallySame (a b : JokeObject) : Bool :=
  decide (genus a = genus b)

/-- Grounded practical sameness: agency and ground-absence must both match. -/
def practicallySame (a b : JokeObject) : Bool :=
  decide (hasAgency a = hasAgency b ∧ isGroundAbsence a = isGroundAbsence b)

/-- Semantic sameness keeps role and practical affordance together. -/
def semanticallySame (a b : JokeObject) : Bool :=
  decide (semanticRole a = semanticRole b ∧ canHoldDrink a = canHoldDrink b)

/-! ## Humor and cringe reuse -/

/-- Humor setup for the one-handle equivalence joke. -/
def topologyHumorSetup : HumorTensegrityQueueKernelBridge.HumorSetup :=
  { complexity := 2
    hComplexity := by decide }

/-- Tensegrity setup: one visible handle, three invisible semantic constraints. -/
def topologyTensegritySetup : HumorTensegrityQueueKernelBridge.TensegritySetup :=
  { visibleNodes := 1
    invisibleTension := 3
    integrity := 4
    hTension := by decide
    hIntegrity := by decide }

/-- A crisp joke leaves little silence debt. -/
def crispCringeState : AffectLabelingPatternInterrupt.StallBackoffState :=
  { failures := 0, baseDelay := 1, baseSilence := 1 }

/-- An overexplained joke accumulates cringe vacuum. -/
def overexplainedCringeState : AffectLabelingPatternInterrupt.StallBackoffState :=
  { failures := 2, baseDelay := 1, baseSilence := 1 }

/-- Concrete mechanism classifier for the topologist joke family. -/
def mechanismOfPair (a b : JokeObject) : HumorMechanism :=
  if jokeTopologicallySame a b then
    if semanticallySame a b then .topologicalCollapse else .semanticSnapback
  else if isGroundAbsence a || isGroundAbsence b then
    .boundaryCondition
  else
    .cringeLeak

/-- "Max effect" for these jokes: collapse first, then snap back semantically,
with less cringe than the overexplained form. -/
def maxEffectPair (a b : JokeObject) : Bool :=
  jokeTopologicallySame a b &&
    not (semanticallySame a b) &&
    decide (AffectLabelingPatternInterrupt.cringeVacuum crispCringeState <
      AffectLabelingPatternInterrupt.cringeVacuum overexplainedCringeState)

/-- Betty's first question: at the coarse topological level, donut and mug match. -/
theorem donut_and_mug_topologically_match :
    jokeTopologicallySame .donut .coffeeMug = true := by
  decide

/-- The practical counterpoint: head and ground hole do not match. -/
theorem head_and_ground_hole_practically_differ :
    practicallySame .head .groundHole = false := by
  decide

/-- The reused humor bridge gives the topologist joke positive setup budget. -/
theorem topology_humor_budget_positive :
    0 < HumorTensegrityQueueKernelBridge.humorTensegrityFailureBudget
      topologyHumorSetup topologyTensegritySetup :=
  HumorTensegrityQueueKernelBridge.humor_tensegrity_budget_positive
    topologyHumorSetup topologyTensegritySetup

/-- The crisp version has less cringe vacuum than the overexplained version. -/
theorem crisp_has_less_cringe_than_overexplained :
    AffectLabelingPatternInterrupt.cringeVacuum crispCringeState <
      AffectLabelingPatternInterrupt.cringeVacuum overexplainedCringeState := by
  decide

/-- The cafe version gets maximum effect: topology collapses, then breakfast semantics snaps back. -/
theorem donut_mug_max_effect :
    maxEffectPair .donut .coffeeMug = true := by
  decide

/-- Coffee gone: the carrier topology remains, but the drinkable content vanishes. -/
theorem coffee_gone_is_boundary_condition :
    jokeTopologicallySame .coffeeMug .emptyMug = true ∧
      isDrinkable .coffee = true ∧
      isDrinkable .emptyMug = false := by
  decide

/-- The bar-handle question: the handle has genus-like loop content but not container semantics. -/
theorem bar_handle_loop_not_beer_container :
    genus .barHandle = 1 ∧ canHoldDrink .barHandle = false := by
  decide

/-- The butter test: donut and mug match coarsely but not semantically. -/
theorem do_not_butter_the_mug :
    jokeTopologicallySame .donut .coffeeMug = true ∧
      acceptsButter .donut = true ∧
      acceptsButter .coffeeMug = false ∧
      canHoldDrink .coffeeMug = true ∧
      canHoldDrink .donut = false ∧
      mechanismOfPair .donut .coffeeMug = .semanticSnapback := by
  decide

/-- The barista objection: donut and mug match coarsely but not semantically. -/
theorem do_not_drink_the_donut :
    jokeTopologicallySame .donut .coffeeMug = true ∧
      semanticallySame .donut .coffeeMug = false ∧
      mechanismOfPair .donut .coffeeMug = .semanticSnapback ∧
      canHoldDrink .coffeeMug = true ∧
      canHoldDrink .donut = false := by
  decide

/-- Knife-fight ambiguity: donut and proof are not the same semantic role,
even if neither is weapon-like. -/
theorem donut_knife_proof_ambiguity :
    isWeaponLike .knife = true ∧
      isWeaponLike .donut = false ∧
      semanticRole .donut ≠ semanticRole .proof := by
  decide

/-- Key-loss joke: same connected room story is too coarse to recover the keys. -/
theorem keys_connected_to_room_is_not_location :
    jokeTopologicallySame .keys .room = true ∧
      semanticallySame .keys .room = false := by
  decide

/-- The closing tag: head/hole is not a topology gag only; it routes through practical boundary. -/
theorem head_hole_routes_to_boundary_not_identity :
    mechanismOfPair .head .groundHole = .boundaryCondition ∧
      practicallySame .head .groundHole = false := by
  decide

/-- The whole bounded joke certificate. -/
theorem topologist_joke_certificate :
    jokeTopologicallySame .donut .coffeeMug = true ∧
      semanticallySame .donut .coffeeMug = false ∧
      mechanismOfPair .donut .coffeeMug = .semanticSnapback ∧
      maxEffectPair .donut .coffeeMug = true ∧
      acceptsButter .donut = true ∧
      acceptsButter .coffeeMug = false ∧
      practicallySame .head .groundHole = false ∧
      hasAgency .head = true ∧
      isGroundAbsence .groundHole = true ∧
      jokeTopologicallySame .coffeeMug .emptyMug = true ∧
      isDrinkable .emptyMug = false ∧
      AffectLabelingPatternInterrupt.cringeVacuum crispCringeState <
        AffectLabelingPatternInterrupt.cringeVacuum overexplainedCringeState := by
  decide

end TopologistJokeWitness
end Gnosis
