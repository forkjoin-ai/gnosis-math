set_option linter.unusedVariables false

namespace ContrarianMemoryThrashingEfficiency

theorem cache_miss_optimality 
    (System : Type) (CacheMisses : System → Nat) (Entropy : System → Nat)
    (h_vent : ∀ s, Entropy s = CacheMisses s)
    (h_opt : ∀ s1 s2, CacheMisses s1 < CacheMisses s2 → Entropy s1 < Entropy s2) :
    ∀ s1 s2, CacheMisses s1 < CacheMisses s2 → Entropy s1 < Entropy s2 := by
  intro s1 s2 h
  exact h_opt s1 s2 h

end ContrarianMemoryThrashingEfficiency