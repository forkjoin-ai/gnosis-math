/-!
# Coarse Bucket Sketch

Concrete `Fin 3 -> Fin 2` two-bucket collapse witness.
-/

namespace PlanetaryHomologySandbox

def coarseTwoBucket : Fin 3 → Fin 2
  | ⟨0, _⟩ => ⟨0, by decide⟩
  | ⟨1, _⟩ => ⟨1, by decide⟩
  | ⟨_, _⟩ => ⟨0, by decide⟩

theorem coarseTwoBucket_zero_two_collision :
    coarseTwoBucket ⟨0, by decide⟩ =
      coarseTwoBucket ⟨2, by decide⟩ := by
  rfl

theorem coarseTwoBucket_zero_two_distinct :
    (⟨0, by decide⟩ : Fin 3) ≠ ⟨2, by decide⟩ := by
  intro h
  have hVal : (0 : Nat) = 2 := Fin.val_eq_of_eq h
  contradiction

theorem coarseTwoBucket_not_injective_three :
    ¬ Function.Injective coarseTwoBucket := by
  intro hInjective
  exact coarseTwoBucket_zero_two_distinct
    (hInjective coarseTwoBucket_zero_two_collision)

end PlanetaryHomologySandbox
