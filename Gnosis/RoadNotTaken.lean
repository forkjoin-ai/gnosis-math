/-
  RoadNotTaken.lean
  =================

  Robert Frost, "The Road Not Taken" (1916), as an instance of the extracted
  cause-and-effect core.

      Two roads diverged in a yellow wood,
      ...
      I took the one less traveled by,
      And that has made all the difference.

  The poem is, exactly, a theorem about counterfactual causation at a fork:

    * "Two roads diverged"  = the FORK — the branch point, the +1 declination off
      a single path. The fork is the swerve (`ChickieRunSwerveGame.Move.swerve`,
      the clinamen) made into a choice.

    * the famous irony — "the passing there had worn them really about the same"
      — the two roads are SYMMETRIC. There is no intrinsic difference in the
      terrain.

    * "and that has made all the difference"  = the choice is a DIFFERENCE-MAKER
      (`CauseAndEffect.IsDifferenceMaker`). The outcome depends counterfactually
      on which road is taken.

  Put together: the difference is not in the roads (they are the same) but in the
  swerve — the clinamen makes the difference out of symmetry. That is why this
  fits the corpus exactly: a genuine cause over a symmetric substrate, the same
  shape as the cat-map coincidence (equal magnitudes are not a shared invariant)
  and the quality-margin antitheorem. The swerve, not the terrain, is the cause.

  Init-only Rustic Church. No Mathlib, no `omega`, no `simp`/`decide` on
  open-variable goals.
-/
import Gnosis.CauseAndEffect
import Gnosis.ChickieRunSwerveGame

namespace GnosisMath
namespace RoadNotTaken

open GnosisMath.CauseAndEffect (IsDifferenceMaker CausalLaw worlds_disagree)
open GnosisMath.ChickieRunSwerveGame (Move)

-- ══════════════════════════════════════════════════════════
-- THE FORK: TWO ROADS DIVERGED
-- ══════════════════════════════════════════════════════════

/-- The two roads at the diverging fork. -/
inductive Road
  | lessTraveled   -- the one taken: the swerve, the +1
  | wellTrodden    -- the default: the path of least declination
  deriving DecidableEq

/-- "the passing there had worn them really about the same" — both roads are worn
    equally. There is no intrinsic difference in the terrain. -/
def wear : Road → Nat
  | _ => 1

theorem roads_worn_the_same (r1 r2 : Road) : wear r1 = wear r2 := rfl

/-- The road less traveled IS the swerve — the clinamen made a choice. -/
def roadAsMove : Road → Move
  | .lessTraveled => .swerve
  | .wellTrodden  => .stay

theorem road_less_traveled_is_the_swerve :
    roadAsMove .lessTraveled = Move.swerve := rfl

-- ══════════════════════════════════════════════════════════
-- THE CHOICE MAPS TO A LIFE  (a CausalLaw on the fork)
-- ══════════════════════════════════════════════════════════

/-- The two lives the fork leads to. -/
inductive Life
  | divergent   -- the life of the road less traveced
  | usual       -- the life of the well-trodden road
  deriving DecidableEq

def roadSign : Road → Int
  | .lessTraveled => 1
  | .wellTrodden  => 0

def lifeSign : Life → Int
  | .divergent => 1
  | .usual     => 0

def lifeOf : Road → Life
  | .lessTraveled => .divergent
  | .wellTrodden  => .usual

/-- The road less traveced carries the +1 — it is the swerve pole of the fork. -/
theorem less_traveled_is_positive : roadSign Road.lessTraveled = 1 := rfl

/-- The fork is a `CausalLaw`: the choice of road maps, sign-preservingly and
    bijectively, to the life that results. An instance of the general
    cause↦effect mapping. -/
def roadCausalLaw : CausalLaw Road Life where
  causeSign := roadSign
  effectSign := lifeSign
  effectOf := lifeOf
  preserves := fun c => by cases c <;> decide
  surjective := fun e => by
    cases e
    · exact ⟨.lessTraveled, rfl⟩
    · exact ⟨.wellTrodden, rfl⟩
  injective := fun a b h => by cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

-- ══════════════════════════════════════════════════════════
-- "AND THAT HAS MADE ALL THE DIFFERENCE"
-- ══════════════════════════════════════════════════════════

/-- The life that results, as a function of whether the swerve is removed:
    `false` = took the road less traveced (the swerve fired) → the divergent
    life; `true` = the swerve removed → the divergent life never arrives. -/
def arrivedDivergent : Bool → Prop
  | false => True
  | true  => False

/-- **And that has made all the difference.** The choice at the fork is a genuine
    counterfactual cause: the divergent life arrives with the swerve and not
    without it. -/
theorem made_all_the_difference : IsDifferenceMaker arrivedDivergent := by
  constructor
  · trivial            -- with the swerve: the divergent life
  · intro h; exact h   -- without it: it never comes

/-- **The difference is in the swerve, not the road.** The two roads are worn the
    same (symmetric, no intrinsic difference), yet the choice makes all the
    difference and the two outcomes genuinely disagree. The clinamen makes the
    difference out of symmetry — the cause is the swerve, not the terrain. -/
theorem difference_is_in_the_swerve_not_the_road :
    (∀ r1 r2 : Road, wear r1 = wear r2) ∧
    IsDifferenceMaker arrivedDivergent ∧
    ¬ (arrivedDivergent false ↔ arrivedDivergent true) :=
  ⟨roads_worn_the_same, made_all_the_difference, worlds_disagree made_all_the_difference⟩

/-- The poem, bundled: two diverging roads worn the same; the road less traveced
    is the swerve (+1); the choice maps to a life (a `CausalLaw`); and that has
    made all the difference. -/
theorem road_not_taken :
    (∀ r1 r2 : Road, wear r1 = wear r2) ∧
    roadAsMove Road.lessTraveled = Move.swerve ∧
    roadSign Road.lessTraveled = 1 ∧
    (∀ c, roadCausalLaw.effectSign (roadCausalLaw.effectOf c) = roadCausalLaw.causeSign c) ∧
    IsDifferenceMaker arrivedDivergent :=
  ⟨roads_worn_the_same, rfl, rfl, roadCausalLaw.preserves, made_all_the_difference⟩

end RoadNotTaken
end GnosisMath
