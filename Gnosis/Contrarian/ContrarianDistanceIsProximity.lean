import Gnosis.Braided.BraidedInfinity

namespace Gnosis

/--
**Distance = Proximity**
Extends `Gnosis.Braided.BraidedInfinity`: in a high-order braid manifold,
nodes that appear "distant" on the linear index are often in immediate
topological proximity due to the recursive winding of the fiber.
-/
structure BraidProximity where
  index_distance : Nat
  topological_proximity : Nat
  braid_winds_back : index_distance > 100 → topological_proximity < 5

theorem distance_is_proximity (p : BraidProximity) (h : p.index_distance > 500) :
    p.topological_proximity < 10 := by
  have h_dist : p.index_distance > 100 := Nat.lt_trans (by decide) h
  have h_prox := p.braid_winds_back h_dist
  exact Nat.lt_trans h_prox (by decide)

end Gnosis
