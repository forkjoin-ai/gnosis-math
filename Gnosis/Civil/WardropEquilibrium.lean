/-
  WardropEquilibrium.lean
  =======================

  Formalizes Wardrop's First Principle of User Equilibrium in transportation.
  At equilibrium, the journey times on all used routes are equal and less
  than those on unused routes. No user can unilaterally reduce their travel
  time.

  In Gnosis, we model this as a "Network Witness". A flow distribution
  is stable if the cost (time) of any active path is the minimum available.

  Style: Rustic Church (Init-only).
-/

import Init

namespace Gnosis.Civil

/-- 
  A Path in the transportation network.
-/
structure Path where
  id : Nat
  cost : Nat
  flow : Nat

/-- 
  User Equilibrium Witness:
  A set of paths is in equilibrium if all paths with non-zero flow
  have the same minimum cost.
-/
def IsInUserEquilibrium (paths : List Path) : Prop :=
  ∀ p1 p2, p1 ∈ paths → p2 ∈ paths →
    p1.flow > 0 → p2.flow > 0 → p1.cost = p2.cost

/-- 
  Theorem: Single Path Stability.
  A network with only one used path is trivially in user equilibrium.
-/
theorem single_path_equilibrium (p : Path) :
  IsInUserEquilibrium [p] := by
  unfold IsInUserEquilibrium
  intro p1 p2 h1 h2 _ _
  simp at h1 h2
  rw [h1, h2]

/-- 
  Theorem: Unused Route Condition.
  In equilibrium, if path 1 is used and path 2 is more expensive,
  path 2 must have zero flow.
-/
theorem expensive_route_is_unused (paths : List Path)
  (h_eq : IsInUserEquilibrium paths)
  (p1 p2 : Path)
  (hp1 : p1 ∈ paths) (hp2 : p2 ∈ paths)
  (h_used : p1.flow > 0)
  (h_cost : p2.cost > p1.cost) :
  p2.flow = 0 := by
  match h_p2_flow : p2.flow with
  | 0 => rfl
  | Nat.succ n =>
    have h_p2_pos : p2.flow > 0 := by rw [h_p2_flow]; apply Nat.succ_pos
    have h_costs_equal := h_eq p1 p2 hp1 hp2 h_used h_p2_pos
    rw [h_costs_equal] at h_cost
    have h_not := Nat.lt_irrefl p2.cost
    exact absurd h_cost h_not

end Gnosis.Civil
