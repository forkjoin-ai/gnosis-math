import Init

namespace TopologicalChemicalMatchings

/-- Molecular graph topologies. -/
inductive MolecularTopology
  | Linear -- Alkane
  | Cyclic -- Cycloalkane
  deriving Inhabited, BEq

/-- 
  The Hosoya index computation for a molecule.
-/
def hosoyaIndex (n : Nat) (topo : MolecularTopology) : Nat :=
  match topo with
  | MolecularTopology.Linear => 
      match n with
      | 0 => 1
      | 1 => 1
      | m + 2 => hosoyaIndex (m + 1) .Linear + hosoyaIndex m .Linear
  | MolecularTopology.Cyclic =>
      match n with
      | 0 => 2 -- L_0
      | 1 => 1 -- L_1
      | m + 2 => hosoyaIndex (m + 1) .Cyclic + hosoyaIndex m .Cyclic
termination_by n

/-- 
  Molecular Matching Sandwich Theorem (Instance).
-/
theorem molecular_matching_sandwich_5 :
  hosoyaIndex 5 .Cyclic > hosoyaIndex 5 .Linear := by
  native_decide

/-- 
  The Periodicity Gain (Instance).
-/
theorem periodicity_gain_5 :
  hosoyaIndex 5 .Cyclic = hosoyaIndex 5 .Linear + hosoyaIndex 3 .Linear := by
  native_decide

end TopologicalChemicalMatchings
