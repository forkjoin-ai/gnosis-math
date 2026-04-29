namespace MoonshotSubductiveToposCohomology

theorem subductive_topos_lifting 
    (Topos : Type) (Cohomology : Topos → Nat)
    (Subduct : Topos → Topos)
    (h_lift : ∀ t, Cohomology (Subduct t) = Cohomology t + 1) :
    ∀ t, Cohomology t < Cohomology (Subduct t) := by
  intro t
  rw [h_lift t]
  apply Nat.lt_succ_self

end MoonshotSubductiveToposCohomology