/-!
# Inverse Problem Projection Sketch

Init-only finite witness for the inverse-problem non-injectivity row.

The historical artifact proved the full real matrix statement: if `m < n`,
then no linear map from `R^n` to `R^m` can be injective.  This replacement
restores the core inverse-problem witness without external linear algebra:
projecting a three-coordinate state to two observed coordinates loses the
hidden coordinate.
-/

namespace PlanetaryHomologySandbox

/-- A three-coordinate latent state. -/
structure Latent3 where
  x : Nat
  y : Nat
  hidden : Nat
deriving Repr, DecidableEq

/-- A two-coordinate observation. -/
structure Observation2 where
  x : Nat
  y : Nat
deriving Repr, DecidableEq

/-- Forward projection that discards the hidden coordinate. -/
def forwardProjection2 (state : Latent3) : Observation2 :=
  { x := state.x, y := state.y }

/-- The zero-hidden and one-hidden states are observationally identical. -/
theorem forwardProjection2_hidden_collision
    (x y : Nat) :
    forwardProjection2 { x := x, y := y, hidden := 0 } =
      forwardProjection2 { x := x, y := y, hidden := 1 } := by
  rfl

/-- The zero-hidden and one-hidden states are distinct latent states. -/
theorem hidden_states_distinct
    (x y : Nat) :
    ({ x := x, y := y, hidden := 0 } : Latent3) ≠
      { x := x, y := y, hidden := 1 } := by
  intro h
  have hHidden : 0 = 1 := by
    exact congrArg Latent3.hidden h
  contradiction

/-- The two-coordinate forward projection is not injective. -/
theorem forwardProjection2_not_injective :
    ¬ Function.Injective forwardProjection2 := by
  intro hInjective
  exact hidden_states_distinct 0 0
    (hInjective (forwardProjection2_hidden_collision 0 0))

/--
Packaging theorem for the ledger: an observation that drops one latent
coordinate has a nontrivial kernel witness.
-/
theorem inverse_projection_kernel_witness :
    ∃ a b : Latent3,
      a ≠ b ∧ forwardProjection2 a = forwardProjection2 b := by
  refine ⟨{ x := 0, y := 0, hidden := 0 },
    { x := 0, y := 0, hidden := 1 }, ?_, ?_⟩
  · exact hidden_states_distinct 0 0
  · exact forwardProjection2_hidden_collision 0 0

/-- Concrete scalar Tikhonov normal-equation coefficient. -/
def tikhonovCoefficient : Nat := 2 * 2 + 1

/-- Concrete scalar Tikhonov right-hand side. -/
def tikhonovRightHandSide : Nat := 2 * 5

/-- The concrete scalar candidate solves the normal equation. -/
theorem scalar_tikhonov_candidate_solves :
    tikhonovCoefficient * 2 = tikhonovRightHandSide := by
  native_decide

/-- The candidate is unique inside the bounded search window used by the toy inverse problem. -/
theorem scalar_tikhonov_candidate_unique_in_window :
    (List.filter (fun x => tikhonovCoefficient * x == tikhonovRightHandSide)
      [0, 1, 2, 3, 4]).length = 1 := by
  native_decide

end PlanetaryHomologySandbox
