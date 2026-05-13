import Init
import Gnosis.BuleyeanProbability
import Gnosis.NonEmpiricalPrediction

namespace Gnosis
namespace NovelInferenceForms

/-!
# Novel inference forms — NEI / Mendeleev anchor

`NonEmpiricalInference` is identified with `NonEmpiricalPrediction.StructuralHole`:
both carry `(neighborRoundsSum, neighborVoidSum)` and use the same complement
interpolation. `THM-NEI-MENDELEEV` is **`nei_mendeleev`** below.
-/

abbrev NonEmpiricalInference :=
  NonEmpiricalPrediction.StructuralHole

def NonEmpiricalInference.predictionWeight (n : NonEmpiricalInference) : Nat :=
  NonEmpiricalPrediction.StructuralHole.interpolationWeight n

theorem nei_mendeleev
    (n : NonEmpiricalInference)
    (bs : BuleyeanSpace)
    (i : Fin bs.numChoices)
    (hR : bs.rounds = n.neighborRoundsSum)
    (hV : bs.voidBoundary i = n.neighborVoidSum) :
    n.predictionWeight = bs.weight i :=
  NonEmpiricalPrediction.mendeleev_is_complement n bs i hR hV

theorem nei_mendeleev_interpolation_eq
    (n : NonEmpiricalInference) :
    n.predictionWeight = NonEmpiricalPrediction.StructuralHole.interpolationWeight n :=
  rfl

/-- Same rounds, more aggregated void ⇒ strictly lower prediction weight (`rejection_reduces_prediction`). -/
theorem nei_structure_dominates
    (n₁ n₂ : NonEmpiricalInference)
    (hR : n₁.neighborRoundsSum = n₂.neighborRoundsSum)
    (hV : n₁.neighborVoidSum < n₂.neighborVoidSum) :
    n₂.predictionWeight < n₁.predictionWeight :=
  NonEmpiricalPrediction.rejection_reduces_prediction n₁ n₂ hR hV

/-- Bundle: NEI agrees with Buleyean weight and stays positive (ledger-facing slice). -/
theorem nei_novel_bundle
    (n : NonEmpiricalInference)
    (bs : BuleyeanSpace)
    (i : Fin bs.numChoices)
    (hR : bs.rounds = n.neighborRoundsSum)
    (hV : bs.voidBoundary i = n.neighborVoidSum) :
    n.predictionWeight = bs.weight i ∧ 0 < n.predictionWeight :=
  ⟨nei_mendeleev n bs i hR hV, NonEmpiricalPrediction.hole_has_positive_weight n⟩

theorem novel_inference_forms_ledger_anchor (n : Nat) : Nat.succ n = n + 1 := by
  exact Nat.succ_eq_add_one n

end NovelInferenceForms
end Gnosis
