namespace BuleyeanMath

structure ArchitecturalExpansionJoint where
  stress_load : Nat
  gap_tolerance : Nat
  prevents_fracture : stress_load ≤ gap_tolerance

theorem gap_prevents_structural_fracture (a : ArchitecturalExpansionJoint) :
    a.stress_load ≤ a.gap_tolerance := by
  exact a.prevents_fracture

end BuleyeanMath