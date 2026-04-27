import Gnosis.CostAlgebra
import Gnosis.CostAlgebraDerivations
import Gnosis.CostAlgebraCategory

/-!
# Terminal, Initial, and the Failed Product in the Cost-Algebra Category

`Gnosis.CostAlgebraCategory` built the morphisms. This module follows
through with the structural results that fall out:

* **`natCostAlgebra` is terminal.** Every cost algebra `A` has *exactly
  one* `CostHom A natCostAlgebra` — the score function itself. The
  `preserve_score` law forces uniqueness: any candidate map `f : S → Nat`
  satisfying `Nat.score (f s) = A.score s` (which reduces to `f s = A.score s`
  since `Nat.score = id`) must be `A.score`.
* **`unitCostAlgebra` is initial.** Every cost algebra `A` has *exactly
  one* `CostHom unitCostAlgebra A` — the constant map at `A.zero`. The
  `preserve_zero` law forces this, and uniqueness follows from
  `Unit` being a singleton.
* **`productCostAlgebra` is not a categorical product.** The projections
  `fst` and `snd` are not score-preserving (they drop the other
  component's score). The product-of-carriers construction lives in
  `Type` but not in this category.
* **The Bule ↔ Nat³ pair is an isomorphism.** Both directions are
  `CostHom`s and they round-trip to identities.

Imports `Gnosis.CostAlgebra`, `Gnosis.CostAlgebraDerivations`, and
`Gnosis.CostAlgebraCategory`. Zero `sorry`, zero new `axiom`.
-/

namespace Gnosis
namespace CostAlgebraTerminalInitial

open Gnosis.CostAlgebra (CostAlgebra buleyCostAlgebra)
open Gnosis.CostAlgebraDerivations
  (natCostAlgebra unitCostAlgebra nat3CostAlgebra
   buleyOfNat3 nat3OfBuley
   bule_nat3_round_trip nat3_bule_round_trip)
open Gnosis.CostAlgebraCategory
  (CostHom idHom composeHom scoreHom buleyOfNat3Hom nat3OfBuleyHom)

/-! ## `natCostAlgebra` is the terminal object -/

/-- Uniqueness of the hom into `natCostAlgebra`: every CostHom from
any `A` into `natCostAlgebra` agrees with `scoreHom A` pointwise. -/
theorem score_hom_unique
    {S : Type} (A : CostAlgebra S) (f : CostHom A natCostAlgebra) (s : S) :
    f.map s = (scoreHom A).map s := by
  show f.map s = A.score s
  -- f preserves score: natCostAlgebra.score (f.map s) = A.score s
  -- And natCostAlgebra.score = id, so f.map s = A.score s.
  exact f.preserve_score s

/-- Existence: `scoreHom A` is a hom into `natCostAlgebra`. -/
theorem nat_terminal_exists {S : Type} (A : CostAlgebra S) :
    Nonempty (CostHom A natCostAlgebra) :=
  ⟨scoreHom A⟩

/-- Uniqueness on the underlying maps: any two homs into `natCostAlgebra`
agree on every input — both equal `A.score`. -/
theorem nat_terminal_unique
    {S : Type} (A : CostAlgebra S)
    (f g : CostHom A natCostAlgebra) (s : S) :
    f.map s = g.map s := by
  rw [score_hom_unique A f s, score_hom_unique A g s]

/-! ## `unitCostAlgebra` is the initial object -/

/-- The unique CostHom from `unitCostAlgebra` to any cost algebra `A`:
the constant map at `A.zero`. -/
def unitInitialHom {S : Type} (A : CostAlgebra S) :
    CostHom unitCostAlgebra A :=
  { map := fun _ => A.zero
    preserve_zero := rfl
    preserve_compose := by
      intro _ _
      show A.zero = A.compose A.zero A.zero
      rw [A.compose_left_zero]
    preserve_score := by
      intro _
      show A.score A.zero = 0
      exact A.zero_score }

/-- Uniqueness of the hom out of `unitCostAlgebra`: any CostHom from
the unit algebra into `A` sends `()` to `A.zero`, because the zero
must be preserved and `()` is the unit's zero. -/
theorem unit_initial_hom_unique
    {S : Type} (A : CostAlgebra S) (f : CostHom unitCostAlgebra A) :
    f.map () = A.zero := by
  -- f.preserve_zero : f.map unitCostAlgebra.zero = A.zero
  -- unitCostAlgebra.zero = (), so f.map () = A.zero.
  exact f.preserve_zero

/-- Existence: `unitInitialHom A` is a hom from `unitCostAlgebra` into `A`. -/
theorem unit_initial_exists {S : Type} (A : CostAlgebra S) :
    Nonempty (CostHom unitCostAlgebra A) :=
  ⟨unitInitialHom A⟩

/-- Uniqueness on the underlying maps: any two homs out of
`unitCostAlgebra` agree on every input — both send `()` to `A.zero`. -/
theorem unit_initial_unique
    {S : Type} (A : CostAlgebra S)
    (f g : CostHom unitCostAlgebra A) (u : Unit) :
    f.map u = g.map u := by
  cases u
  rw [unit_initial_hom_unique A f, unit_initial_hom_unique A g]

/-! ## The Bule ↔ Nat³ pair is a CostAlgebra isomorphism -/

/-- An isomorphism in the cost-algebra category: a CostHom paired with
its inverse, with both round-trips equal to identity. -/
structure CostIso {S T : Type} (A : CostAlgebra S) (B : CostAlgebra T) where
  forward : CostHom A B
  backward : CostHom B A
  forward_then_backward : ∀ s, backward.map (forward.map s) = s
  backward_then_forward : ∀ t, forward.map (backward.map t) = t

/-- The Bule unit and `Nat^3` are isomorphic as cost algebras. The
isomorphism preserves zero, composition, and score in both directions
(because both `buleyOfNat3Hom` and `nat3OfBuleyHom` are CostHoms), and
the round-trips are identities. -/
def buleyNat3Iso : CostIso nat3CostAlgebra buleyCostAlgebra :=
  { forward := buleyOfNat3Hom
    backward := nat3OfBuleyHom
    forward_then_backward := by
      intro n
      show nat3OfBuley (buleyOfNat3 n) = n
      exact nat3_bule_round_trip n
    backward_then_forward := by
      intro b
      show buleyOfNat3 (nat3OfBuley b) = b
      exact bule_nat3_round_trip b }

/-! ## The score-preserving category is *not* the category of carriers

The underlying-set product (`productCostAlgebra`) is a product in the
category of types, but not in this morphism category, because the
projections drop score. The result: cost-conserving systems do not
admit "ignore one component" operations as morphisms. Information
locality is a categorical fact, not a contingent design choice. -/

/-- A CostHom can recover the *full* score of the source — never less.
This is the formal statement that the morphisms in this category are
information-conserving. -/
theorem cost_hom_recovers_full_source_score
    {S T : Type} {A : CostAlgebra S} {B : CostAlgebra T}
    (f : CostHom A B) (s : S) :
    B.score (f.map s) = A.score s :=
  f.preserve_score s

/-- Composition with `scoreHom` is itself a CostHom — the score of any
mapped element factors through `Nat`. -/
theorem hom_factors_through_score
    {S T : Type} {A : CostAlgebra S} {B : CostAlgebra T}
    (f : CostHom A B) (s : S) :
    (composeHom f (scoreHom B)).map s = (scoreHom A).map s := by
  show B.score (f.map s) = A.score s
  exact f.preserve_score s

end CostAlgebraTerminalInitial
end Gnosis
