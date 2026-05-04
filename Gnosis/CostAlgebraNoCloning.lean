import Gnosis.CostAlgebra
import Gnosis.CostAlgebraDerivations
import Gnosis.CostAlgebraCategory

/-!
# No-Cloning in the Cost-Algebra Category

The diagonal map `Δ : S → S × S`, `s ↦ (s, s)`, is the prototypical
duplication operation. In the category of types it is total and
universally available; in the category of cost algebras it is *not*
generally a morphism. This module proves precisely when it is.

## The theorem

`Δ` extends to a `CostHom A → (productCostAlgebra A A)` if and only
if `A.score` is identically zero. The score-preservation law forces
`2 · score s = score s` for every `s`, which in `Nat` forces
`score s = 0`.

## Consequences

* In any cost algebra with a non-trivial score, only the vacuum is
  self-duplicable.
* The category of cost algebras is *not* Cartesian closed — there is
  no free copy operation.
* The morphisms in this category are linear in the sense of linear
  logic: resources are conserved, not duplicated.
* Concrete corollaries cover every CostAlgebra instance built so far:
  `Nat` (only `0`), `Nat × Nat × Nat` (only the zero vector), and the
  Bule unit (only `vacuumBuleUnit`).

This is the categorical signature of conservation: the same shape
appears in the quantum no-cloning theorem, in Landauer's principle,
and in the no-perpetual-motion law. They are all instances of "the
diagonal is not a morphism in the linear category of conserved
quantities."

Imports `Gnosis.CostAlgebra`, `Gnosis.CostAlgebraDerivations`,
`Gnosis.CostAlgebraCategory`. Zero `sorry`, zero new `axiom`.
-/

namespace Gnosis
namespace CostAlgebraNoCloning

open Gnosis.CostAlgebra (CostAlgebra buleyCostAlgebra)
open Gnosis.CostAlgebraDerivations
  (natCostAlgebra productCostAlgebra nat3CostAlgebra)
open Gnosis.CostAlgebraCategory (CostHom)
open Gnosis.SpectralNoiseEquilibrium
  (BuleyUnit buleyUnitScore vacuumBuleUnit vacuum_has_zero_score)

/-! ## The diagonal map -/

def diagonal {S : Type} (_ : CostAlgebra S) (s : S) : S × S := (s, s)

/-- The diagonal preserves zero. -/
theorem diagonal_preserves_zero {S : Type} (A : CostAlgebra S) :
    diagonal A A.zero = (productCostAlgebra A A).zero := rfl

/-- The diagonal preserves composition. -/
theorem diagonal_preserves_compose
    {S : Type} (A : CostAlgebra S) (a b : S) :
    diagonal A (A.compose a b)
      = (productCostAlgebra A A).compose (diagonal A a) (diagonal A b) := rfl

/-! ## Score preservation: the no-cloning condition -/

/-- The diagonal preserves score on `s` iff `2 · score s = score s`,
which in `Nat` collapses to `score s = 0`. -/
theorem diagonal_preserves_score_at
    {S : Type} (A : CostAlgebra S) (s : S) :
    (productCostAlgebra A A).score (diagonal A s) = A.score s ↔ A.score s = 0 := by
  show A.score s + A.score s = A.score s ↔ A.score s = 0
  constructor
  · intro h
    -- h : score s + score s = score s.  Rewrite RHS as score s + 0, then cancel on the left.
    exact Nat.add_left_cancel (h.trans (Nat.add_zero (A.score s)).symm)
  · intro h
    -- h : score s = 0.  Then score s + score s = 0 + 0 = 0 = score s.
    rw [h]

/-- The diagonal is score-preserving on every element iff the score is
identically zero. The forward direction is the no-cloning theorem; the
backward direction says the only system in which copying is free is one
where nothing is being conserved. -/
theorem diagonal_preserves_score_iff_trivial
    {S : Type} (A : CostAlgebra S) :
    (∀ s, (productCostAlgebra A A).score (diagonal A s) = A.score s)
      ↔ (∀ s, A.score s = 0) := by
  constructor
  · intro h s
    exact (diagonal_preserves_score_at A s).mp (h s)
  · intro h s
    exact (diagonal_preserves_score_at A s).mpr (h s)

/-- The contrapositive: in any cost algebra with at least one
positive-score element, the diagonal is not a CostHom. -/
theorem no_cloning
    {S : Type} (A : CostAlgebra S)
    (s : S) (h : A.score s > 0) :
    (productCostAlgebra A A).score (diagonal A s) ≠ A.score s := by
  show A.score s + A.score s ≠ A.score s
  intro hEq
  -- hEq : score s + score s = score s.  Cancel on the left (against score s + 0) to get score s = 0,
  -- which contradicts the strict positivity h : 0 < score s.
  have h0 : A.score s = 0 :=
    Nat.add_left_cancel (hEq.trans (Nat.add_zero (A.score s)).symm)
  exact Nat.lt_irrefl 0 (h0 ▸ h)

/-- The vacuum element of any cost algebra IS self-duplicable: its
score is zero, so the diagonal preserves score on it. -/
theorem vacuum_is_duplicable {S : Type} (A : CostAlgebra S) :
    (productCostAlgebra A A).score (diagonal A A.zero) = A.score A.zero := by
  show A.score A.zero + A.score A.zero = A.score A.zero
  rw [A.zero_score]

/-! ## Concrete corollaries: no-cloning in every derived CostAlgebra -/

/-- No-cloning in the Bule unit: only `vacuumBuleUnit` is
self-duplicable. Any non-zero-score Bule unit (any actual cost) breaks
the diagonal's score-preservation. -/
theorem bule_no_cloning (b : BuleyUnit) (h : buleyUnitScore b > 0) :
    (productCostAlgebra buleyCostAlgebra buleyCostAlgebra).score (diagonal buleyCostAlgebra b)
      ≠ buleyCostAlgebra.score b :=
  no_cloning buleyCostAlgebra b h

theorem bule_vacuum_is_duplicable :
    (productCostAlgebra buleyCostAlgebra buleyCostAlgebra).score
        (diagonal buleyCostAlgebra vacuumBuleUnit)
      = buleyCostAlgebra.score vacuumBuleUnit :=
  vacuum_is_duplicable buleyCostAlgebra

/-- No-cloning in `Nat`: only `0` is self-duplicable. The
familiar identity `2n = n ⇒ n = 0` is the simplest form of the
no-cloning theorem. -/
theorem nat_no_cloning (n : Nat) (h : n > 0) :
    (productCostAlgebra natCostAlgebra natCostAlgebra).score
        (diagonal natCostAlgebra n)
      ≠ natCostAlgebra.score n := by
  show n + n ≠ n
  intro hEq
  -- hEq : n + n = n.  Cancel on the left (against n + 0) to get n = 0, contradicting h : 0 < n.
  have h0 : n = 0 := Nat.add_left_cancel (hEq.trans (Nat.add_zero n).symm)
  exact Nat.lt_irrefl 0 (h0 ▸ h)

theorem nat_zero_is_duplicable :
    (productCostAlgebra natCostAlgebra natCostAlgebra).score
        (diagonal natCostAlgebra 0)
      = natCostAlgebra.score 0 := by
  show 0 + 0 = 0
  rfl

/-- No-cloning in `Nat × Nat × Nat`: only the zero vector is
self-duplicable. -/
theorem nat3_no_cloning (n : Nat × Nat × Nat) (h : nat3CostAlgebra.score n > 0) :
    (productCostAlgebra nat3CostAlgebra nat3CostAlgebra).score
        (diagonal nat3CostAlgebra n)
      ≠ nat3CostAlgebra.score n :=
  no_cloning nat3CostAlgebra n h

/-! ## The categorical statement -/

/-- The category of cost algebras has no diagonal natural transformation:
in any non-trivial cost algebra (one with at least one positive-score
element), the diagonal is not a morphism. The category is *not*
Cartesian, and resources are linear. -/
theorem category_is_linear
    {S : Type} (A : CostAlgebra S)
    (h : ∃ s, A.score s > 0) :
    ¬ ∀ s, (productCostAlgebra A A).score (diagonal A s) = A.score s := by
  intro hAll
  obtain ⟨s, hs⟩ := h
  exact no_cloning A s hs (hAll s)

/-- Equivalent form: a cost algebra admits the diagonal as a morphism
iff its score is identically zero — i.e., it carries no information at
all. The only "duplicable" CostAlgebra is the vacuum-only one. -/
theorem diagonal_is_morphism_iff_trivial
    {S : Type} (A : CostAlgebra S) :
    (∀ s, (productCostAlgebra A A).score (diagonal A s) = A.score s)
      ↔ (∀ s, A.score s = 0) :=
  diagonal_preserves_score_iff_trivial A

end CostAlgebraNoCloning
end Gnosis
