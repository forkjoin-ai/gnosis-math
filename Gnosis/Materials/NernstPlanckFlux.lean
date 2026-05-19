import Init

/-
  NernstPlanckFlux.lean
  =====================

  Formalizes the Nernst-Planck flux witness for charged species.
  The total flux (J) is driven by the concentration gradient (diffusion)
  and the electric potential gradient (migration):
  J = -D (∇c + (zF/RT) c ∇φ)

  In Gnosis, we model this as a witness of combined driving forces.
  Stability in electrochemical systems requires the balance of these
  gradients.

  Style: Rustic Church (Init-only).
-/


namespace Gnosis.Materials

/-- 
  Driving Forces for Transport.
-/
structure DrivingForces where
  diffusion_grad : Int
  migration_grad : Int

/-- 
  The Nernst-Planck Flux Witness (J).
  Modeling flux as the sum of driving forces.
-/
def NernstPlanckFlux (d : Int) (forces : DrivingForces) : Int :=
  d * (forces.diffusion_grad + forces.migration_grad)

/-- 
  Theorem: Zero Gradient Zero Flux.
  If both concentration and electric potential gradients are zero,
  the net flux witness is zero.
-/
theorem zero_gradient_zero_flux (d : Int) :
  NernstPlanckFlux d ⟨0, 0⟩ = 0 := by
  unfold NernstPlanckFlux
  rw [Int.add_zero]
  apply Int.mul_zero

/-- 
  Theorem: Diffusion Migration Cancellation.
  Flux is zero if the migration force perfectly opposes the
  diffusion force (Electrochemical Equilibrium).
-/
theorem electrochemical_equilibrium (d f : Int) :
  NernstPlanckFlux d ⟨f, -f⟩ = 0 := by
  unfold NernstPlanckFlux
  rw [Int.add_right_neg]
  apply Int.mul_zero

end Gnosis.Materials
