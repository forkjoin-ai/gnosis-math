namespace ForkRaceFold

structure SemanticCategory where
  friction : Nat
  adjunction_power : Nat

theorem semantic_friction_bypass (c : SemanticCategory) (h1 : c.adjunction_power ≥ c.friction) :
  c.adjunction_power - c.friction + c.friction = c.adjunction_power := by
  exact Nat.sub_add_cancel h1

end ForkRaceFold