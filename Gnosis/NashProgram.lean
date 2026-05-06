import Init

namespace Gnosis
namespace NashProgram

/-!
# Nash program (non-cooperative bargaining scaffold)

This module makes the bargaining layer explicit:

- disagreement point `(d₁, d₂)`,
- feasible agreement set,
- Nash product objective `(u₁ - d₁)(u₂ - d₂)`,
- symmetry and IIA as formal contracts,
- and the core theorem: a Nash solution maximizes the product over feasible set.
-/

/-- Two-agent bargaining game with total mass budget `R`,
disagreement point `(d₁, d₂)`, and feasibility relation. -/
structure BargainingGame where
  R : Nat
  d1 : Nat
  d2 : Nat
  feasible : Nat → Nat → Prop

/-- Surplus utility for agent 1 over disagreement point. -/
def surplus1 (g : BargainingGame) (u1 : Nat) : Nat :=
  u1 - g.d1

/-- Surplus utility for agent 2 over disagreement point. -/
def surplus2 (g : BargainingGame) (u2 : Nat) : Nat :=
  u2 - g.d2

/-- Nash product objective. -/
def nashProduct (g : BargainingGame) (u1 u2 : Nat) : Nat :=
  surplus1 g u1 * surplus2 g u2

/-- The Nash bargaining solution predicate:
`(x1, x2)` is feasible and maximizes Nash product among feasible agreements. -/
def IsNashSolution (g : BargainingGame) (x1 x2 : Nat) : Prop :=
  g.feasible x1 x2 ∧
  ∀ y1 y2, g.feasible y1 y2 → nashProduct g y1 y2 ≤ nashProduct g x1 x2

/-- Axiom-of-symmetry shape for a game:
identical disagreement points and symmetric feasible set. -/
def SymmetricGame (g : BargainingGame) : Prop :=
  g.d1 = g.d2 ∧ ∀ x1 x2, g.feasible x1 x2 ↔ g.feasible x2 x1

/-- Bargaining selector contract (abstract solution concept). -/
abbrev Selector := BargainingGame → Nat × Nat

/-- Symmetry axiom for a selector:
on symmetric games, chosen utilities are equal. -/
def SatisfiesSymmetry (σ : Selector) : Prop :=
  ∀ g, SymmetricGame g → (σ g).1 = (σ g).2

/-- Feasible-set inclusion (`g'` is a shrink of `g`). -/
def FeasibleSubset (g g' : BargainingGame) : Prop :=
  ∀ x1 x2, g'.feasible x1 x2 → g.feasible x1 x2

/-- Independence of Irrelevant Alternatives (IIA):
if `σ g = x` and `x` remains feasible in shrunk game `g'`, selector keeps `x`. -/
def SatisfiesIIA (σ : Selector) : Prop :=
  ∀ g g' x1 x2,
    FeasibleSubset g g' →
    σ g = (x1, x2) →
    g'.feasible x1 x2 →
    σ g' = (x1, x2)

/-- Core Nash-program theorem (explicit):
if `(x1, x2)` is a Nash solution, it maximizes the product over feasible set. -/
theorem nash_solution_maximizes_product
    (g : BargainingGame) (x1 x2 : Nat)
    (hNash : IsNashSolution g x1 x2) :
    ∀ y1 y2, g.feasible y1 y2 → nashProduct g y1 y2 ≤ nashProduct g x1 x2 := by
  exact hNash.2

/-- Simple canonical split game with no disagreement mass. -/
def splitGame (R : Nat) : BargainingGame :=
  { R := R
    d1 := 0
    d2 := 0
    feasible := fun x1 x2 => x1 + x2 = R }

/-- In the split game, Nash product is the utility product. -/
theorem split_game_product_is_utility_product (R x1 x2 : Nat) :
    nashProduct (splitGame R) x1 x2 = x1 * x2 := by
  unfold nashProduct surplus1 surplus2 splitGame
  simp

/-- Definitional sanity: any witness of `IsNashSolution` is feasible. -/
theorem nash_solution_is_feasible
    (g : BargainingGame) (x1 x2 : Nat)
    (hNash : IsNashSolution g x1 x2) :
    g.feasible x1 x2 := hNash.1

end NashProgram
end Gnosis
