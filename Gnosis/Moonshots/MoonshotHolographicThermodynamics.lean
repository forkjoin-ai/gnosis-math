namespace MoonshotHolographicThermodynamics

theorem holographic_thermodynamic_bound 
    (State : Type) (Entropy : State → Nat)
    (Boundary : State → State)
    (h_bound : ∀ s, Entropy s ≤ Entropy (Boundary s)) :
    ∀ s, Entropy s ≤ Entropy (Boundary s) := by
  intro s
  exact h_bound s

end MoonshotHolographicThermodynamics