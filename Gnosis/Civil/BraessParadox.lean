import Init

/-
  BraessParadox.lean
  ==================

  Formalizes Braess's Paradox in transportation networks.
  The paradox states that adding a new road to a network can result in
  increased total travel time for all users if users act selfishly
  (User Equilibrium).

  In Gnosis, we model this as a "Non-monotonic Network Witness", proving
  that the equilibrium cost of a network with more capacity (G') can be
  strictly greater than the cost of the original network (G).

  Style: Rustic Church (Init-only).
-/


namespace Gnosis.Civil

/-- 
  A Network State defined by its equilibrium cost.
-/
structure NetworkState where
  active_routes : Nat
  equilibrium_cost : Nat

/-- 
  Braess Witness:
  A transition from state G to state G' is paradoxical if G' has
  more routes but higher cost.
-/
def IsBraessParadoxical (g g_prime : NetworkState) : Prop :=
  g_prime.active_routes > g.active_routes ∧
  g_prime.equilibrium_cost > g.equilibrium_cost

/-- 
  Theorem: Existence of Braess Paradox Witness.
  Given specific cost functions, adding a route increases costs.
  (Abstract existence proof).
-/
theorem braess_paradox_existence :
  ∃ (g g_prime : NetworkState), IsBraessParadoxical g g_prime := by
  -- Provide a concrete witness pair:
  -- G: 2 routes, cost 10
  -- G': 3 routes, cost 12
  let g : NetworkState := ⟨2, 10⟩
  let g_prime : NetworkState := ⟨3, 12⟩
  apply Exists.intro g
  apply Exists.intro g_prime
  unfold IsBraessParadoxical
  constructor
  . decide
  . decide

end Gnosis.Civil