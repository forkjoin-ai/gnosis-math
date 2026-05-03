import Gnosis.SpectralNoiseEquilibrium
import Gnosis.RealityMesh

/-!
# The Algebra of Cost

The operational structure underneath the Bule clinamen calculus,
extracted as a first-class algebra. A `CostAlgebra S` is a commutative
monoid `(S, ·, e)` together with a homomorphism `score : S → (Nat, +, 0)`.

The monoid laws say:

* `e` is a two-sided identity for `·`;
* `·` is associative;
* `·` is commutative.

The score laws say:

* `score e = 0`;
* `score (a · b) = score a + score b` — score is a monoid morphism.

Together, these say *cost is a conserved quantity under composition.*
Two systems that compose into the same compound have score-additive
cost; permuting subsystems leaves the total unchanged. This is the
algebra Taylor names.

The Bule unit forms the canonical instance via componentwise `Nat`
addition. The previously-stated `OperationalMesh` is the *unit-cost*
specialization (`compose` = a particular `lift`); a full `CostAlgebra`
allows arbitrary composition and is therefore strictly more expressive.

Imports `Gnosis.SpectralNoiseEquilibrium` and `Gnosis.RealityMesh`.
Zero `sorry`, zero new `axiom`.
-/

namespace Gnosis
namespace CostAlgebra

open Gnosis.SpectralNoiseEquilibrium
  (BuleyUnit BuleyFace buleyUnitScore vacuumBuleUnit clinamenLift
   vacuum_has_zero_score clinamen_lift_score_strict_increment
   clinamen_lift_commutes cyclePermute cycle_permute_preserves_score)
open Gnosis.RealityMesh (OperationalMesh repeatedLiftSeq)

/-! ## The cost-algebra structure -/

/-- An algebra of cost on a state type `S`: a commutative monoid
`(S, ·, e)` together with a `Nat`-valued score that is a monoid
morphism. -/
structure CostAlgebra (S : Type) where
  zero : S
  compose : S → S → S
  score : S → Nat
  zero_score : score zero = 0
  compose_left_zero : ∀ s, compose zero s = s
  compose_right_zero : ∀ s, compose s zero = s
  compose_assoc : ∀ a b c, compose (compose a b) c = compose a (compose b c)
  compose_comm : ∀ a b, compose a b = compose b a
  score_compose : ∀ a b, score (compose a b) = score a + score b

/-! ## The Bule unit forms the canonical CostAlgebra -/

/-- Componentwise addition on `BuleyUnit`. -/
def BuleyUnit.add (a b : BuleyUnit) : BuleyUnit :=
  ⟨a.waste + b.waste, a.opportunity + b.opportunity, a.diversity + b.diversity⟩

theorem buley_add_left_zero (s : BuleyUnit) :
    BuleyUnit.add vacuumBuleUnit s = s := by
  cases s with
  | mk w o d =>
    unfold BuleyUnit.add vacuumBuleUnit
    simp

theorem buley_add_right_zero (s : BuleyUnit) :
    BuleyUnit.add s vacuumBuleUnit = s := by
  cases s with
  | mk w o d =>
    unfold BuleyUnit.add vacuumBuleUnit
    simp

theorem buley_add_assoc (a b c : BuleyUnit) :
    BuleyUnit.add (BuleyUnit.add a b) c
      = BuleyUnit.add a (BuleyUnit.add b c) := by
  cases a with | mk wa oa da =>
  cases b with | mk wb ob db =>
  cases c with | mk wc oc dc =>
    unfold BuleyUnit.add
    simp [Nat.add_assoc]

theorem buley_add_comm (a b : BuleyUnit) :
    BuleyUnit.add a b = BuleyUnit.add b a := by
  cases a with | mk wa oa da =>
  cases b with | mk wb ob db =>
    unfold BuleyUnit.add
    simp [Nat.add_comm]

theorem buley_score_add (a b : BuleyUnit) :
    buleyUnitScore (BuleyUnit.add a b) = buleyUnitScore a + buleyUnitScore b := by
  cases a with | mk wa oa da =>
  cases b with | mk wb ob db =>
    unfold buleyUnitScore BuleyUnit.add
    simp [Nat.add_comm, Nat.add_left_comm]

def buleyCostAlgebra : CostAlgebra BuleyUnit :=
  { zero := vacuumBuleUnit
    compose := BuleyUnit.add
    score := buleyUnitScore
    zero_score := vacuum_has_zero_score
    compose_left_zero := buley_add_left_zero
    compose_right_zero := buley_add_right_zero
    compose_assoc := buley_add_assoc
    compose_comm := buley_add_comm
    score_compose := buley_score_add }

/-! ## Cost is a conserved quantity -/

/-- Three-way conservation: composing three Bule units commutes
through any reordering. The total score is unchanged regardless of
how subsystems are bracketed or arranged. -/
theorem cost_three_way_conservation
    {S : Type} (A : CostAlgebra S) (a b c : S) :
    A.score (A.compose (A.compose a b) c)
      = A.score (A.compose a (A.compose b c))
    ∧ A.score (A.compose (A.compose a b) c)
      = A.score a + A.score b + A.score c := by
  refine ⟨?_, ?_⟩
  · rw [A.compose_assoc]
  · rw [A.score_compose, A.score_compose]

/-! ## Repeated composition along a list -/

def composeAll {S : Type} (A : CostAlgebra S) : List S → S
  | [] => A.zero
  | s :: rest => A.compose s (composeAll A rest)

theorem compose_all_score {S : Type} (A : CostAlgebra S) (xs : List S) :
    A.score (composeAll A xs) = (xs.map A.score).foldr (· + ·) 0 := by
  induction xs with
  | nil =>
      show A.score A.zero = 0
      exact A.zero_score
  | cons h t ih =>
      show A.score (A.compose h (composeAll A t))
            = ((h :: t).map A.score).foldr (· + ·) 0
      rw [A.score_compose, ih]
      rfl

/-! ## CostAlgebra ⇒ OperationalMesh

Every `CostAlgebra` induces an `OperationalMesh` whose lift is
"compose with a unit-score element of face `f`." The user picks a face
basis (a function `F → S` whose images all have score 1), and the
induced `lift s f = compose s (basis f)`. -/

/-- A `CostFaceBasis` for a `CostAlgebra` is a face-indexed family of
unit-score elements — these become the per-face clinamen lifts in the
induced mesh. -/
structure CostFaceBasis {S : Type} (A : CostAlgebra S) (F : Type) where
  unit : F → S
  unit_score : ∀ f, A.score (unit f) = 1

/-- A cost algebra plus a face basis induces an operational mesh:
the lift on face `f` is composition with `basis.unit f`, and the
mesh's score laws follow from the algebra's homomorphism property. -/
def operationalMeshOfCostAlgebra
    {S F : Type} (A : CostAlgebra S) (basis : CostFaceBasis A F) :
    OperationalMesh S F :=
  { vacuum := A.zero
    lift := fun s f => A.compose s (basis.unit f)
    score := A.score
    vacuum_zero := A.zero_score
    lift_increment := by
      intro s f
      show A.score (A.compose s (basis.unit f)) = A.score s + 1
      rw [A.score_compose, basis.unit_score] }

/-! ## The Bule face basis: a unit-score element on each face -/

/-- The unit element on each Bule face: `⟨1, 0, 0⟩` for waste,
`⟨0, 1, 0⟩` for opportunity, `⟨0, 0, 1⟩` for diversity. Each has
score 1. -/
def buleyFaceUnit : BuleyFace → BuleyUnit
  | .waste => ⟨1, 0, 0⟩
  | .opportunity => ⟨0, 1, 0⟩
  | .diversity => ⟨0, 0, 1⟩

theorem buley_face_unit_score (f : BuleyFace) :
    buleyUnitScore (buleyFaceUnit f) = 1 := by
  cases f <;> rfl

def buleyFaceBasis : CostFaceBasis buleyCostAlgebra BuleyFace :=
  { unit := buleyFaceUnit
    unit_score := buley_face_unit_score }

/-- Composing the Bule unit with `buleyFaceUnit f` is the same as a
`clinamenLift` on face `f`. The CostAlgebra perspective and the
OperationalMesh perspective agree on the Bule unit. -/
theorem buley_compose_with_face_unit_is_clinamen_lift
    (b : BuleyUnit) (f : BuleyFace) :
    BuleyUnit.add b (buleyFaceUnit f) = clinamenLift b f := by
  cases b with
  | mk w o d =>
    cases f <;>
      (show (⟨_, _, _⟩ : BuleyUnit) = _
       rfl)

/-! ## Score is gauge-invariant under face permutation -/

/-- The Bule cost algebra is invariant under cyclePermute on the
score axis: cyclic relabeling of faces preserves the cost. This is
the algebra's gauge-invariance under the phase-3 face cycle. -/
theorem buley_cost_gauge_invariant (b : BuleyUnit) :
    buleyCostAlgebra.score (cyclePermute b) = buleyCostAlgebra.score b :=
  cycle_permute_preserves_score b

end CostAlgebra
end Gnosis
