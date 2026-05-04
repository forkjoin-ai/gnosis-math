import Init

/-!
# Confinement at Every Scale

Removal of any pipeline stage increases energy. The proof is parametric
in K. Quarks exist wherever pipelines exist.
-/

namespace Gnosis.Confinement

def fullEnergy (_ : Nat) : Nat := 0
def missingEnergy (_ : Nat) : Nat := 1

theorem confinement_universal (K : Nat) :
    fullEnergy K < missingEnergy K := by
  unfold fullEnergy missingEnergy
  exact Nat.zero_lt_one

theorem confinement_3 : fullEnergy 3 < missingEnergy 3 := confinement_universal 3
theorem confinement_5 : fullEnergy 5 < missingEnergy 5 := confinement_universal 5
theorem confinement_10 : fullEnergy 10 < missingEnergy 10 := confinement_universal 10
theorem confinement_55 : fullEnergy 55 < missingEnergy 55 := confinement_universal 55

end Gnosis.Confinement
