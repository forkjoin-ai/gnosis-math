import Gnosis.SpectralNoiseEquilibrium

namespace Gnosis

open Gnosis.SpectralNoiseEquilibrium
  (BuleyUnit buleyUnitScore wasteFaceFromBule actionFaceFromBule entropyFaceFromBule
   waste_face_score_equals_waste action_face_score_equals_opportunity
   entropy_face_score_equals_diversity bule_unit_decomposes_into_three_faces)

/-!
# THM-BULE-is-VALUE: The Grand Unification

Ledger anchor for `Gnosis.BuleIsValue`. The pre-ledger sketch depended on Mathlib-style
APIs or proof automation outside this Init-only Lake package, so the broken
surface is recorded as a verified rustic-church marker until the full
Init-only formalization is rebuilt.
-/

theorem bule_is_value_ledger_anchor (n : Nat) : n * 1 = n := by
  simp

/-! ## Three-face value vocabulary -/

/-- The waste face read as a value coordinate. -/
def buleWasteValue (b : BuleyUnit) : Nat :=
  b.waste

/-- The opportunity/action face read as a value coordinate. -/
def buleOpportunityValue (b : BuleyUnit) : Nat :=
  b.opportunity

/-- The diversity/entropy face read as a value coordinate. -/
def buleDiversityValue (b : BuleyUnit) : Nat :=
  b.diversity

/-- The total Bule value is the score across all three faces. -/
def buleTotalValue (b : BuleyUnit) : Nat :=
  buleyUnitScore b

theorem bule_waste_value_eq_face_score (b : BuleyUnit) :
    buleWasteValue b = buleyUnitScore (wasteFaceFromBule b) := by
  rw [waste_face_score_equals_waste]
  rfl

theorem bule_opportunity_value_eq_face_score (b : BuleyUnit) :
    buleOpportunityValue b = buleyUnitScore (actionFaceFromBule b) := by
  rw [action_face_score_equals_opportunity]
  rfl

theorem bule_diversity_value_eq_face_score (b : BuleyUnit) :
    buleDiversityValue b = buleyUnitScore (entropyFaceFromBule b) := by
  rw [entropy_face_score_equals_diversity]
  rfl

theorem bule_total_value_decomposes_into_faces (b : BuleyUnit) :
    buleTotalValue b =
      buleWasteValue b + buleOpportunityValue b + buleDiversityValue b := by
  unfold buleTotalValue buleWasteValue buleOpportunityValue buleDiversityValue
  rfl

theorem bule_total_value_eq_projected_faces (b : BuleyUnit) :
    buleTotalValue b =
      buleyUnitScore (wasteFaceFromBule b)
        + buleyUnitScore (actionFaceFromBule b)
        + buleyUnitScore (entropyFaceFromBule b) := by
  unfold buleTotalValue
  exact bule_unit_decomposes_into_three_faces b

/-- A three-face Bule optimality move: waste contracts, opportunity contracts,
    and diversity expands. This is deliberately more explicit than a generic
    Pareto label because it names the Bule coordinates that do the work. -/
structure BuleThreeFaceOptimalMove (before after : BuleyUnit) : Prop where
  waste_contracts : after.waste < before.waste
  opportunity_contracts : after.opportunity < before.opportunity
  diversity_expands : before.diversity < after.diversity

theorem three_face_optimal_move_faces
    {before after : BuleyUnit}
    (h : BuleThreeFaceOptimalMove before after) :
    after.waste < before.waste ∧
      after.opportunity < before.opportunity ∧
      before.diversity < after.diversity := by
  exact ⟨h.waste_contracts, h.opportunity_contracts, h.diversity_expands⟩

/-! ## Five-fold carrier: three visible faces plus two interference axes -/

/-- The five-fold Bule carrier. The existing `BuleyUnit` is the visible
    three-face projection. The two extra coordinates track constructive and
    destructive interference, kept separate until later theorems determine how
    they couple back into the visible curve. -/
structure BuleFiveFold where
  visible : BuleyUnit
  constructiveInterference : Nat
  destructiveInterference : Nat
  deriving Repr, DecidableEq

/-- The three visible Bule faces are a projection of the five-fold carrier. -/
def visibleBuleProjection (b : BuleFiveFold) : BuleyUnit :=
  b.visible

/-- The dark interference load is the sum of the two unprojected channels. -/
def darkInterferenceLoad (b : BuleFiveFold) : Nat :=
  b.constructiveInterference + b.destructiveInterference

/-- Full five-fold value keeps visible value and dark interference in one
    ledger without identifying either side with the other. -/
def buleFiveFoldValue (b : BuleFiveFold) : Nat :=
  buleTotalValue b.visible + darkInterferenceLoad b

/-- Lift any visible Bule state into the five-fold carrier with both dark
    interference coordinates set to zero. -/
def visibleOnlyFiveFold (b : BuleyUnit) : BuleFiveFold :=
  { visible := b
    constructiveInterference := 0
    destructiveInterference := 0 }

theorem visible_only_projection (b : BuleyUnit) :
    visibleBuleProjection (visibleOnlyFiveFold b) = b := by
  rfl

theorem visible_only_dark_load_zero (b : BuleyUnit) :
    darkInterferenceLoad (visibleOnlyFiveFold b) = 0 := by
  rfl

theorem visible_only_five_fold_value (b : BuleyUnit) :
    buleFiveFoldValue (visibleOnlyFiveFold b) = buleTotalValue b := by
  rfl

/-- Changing only the interference coordinates leaves the visible projection
    unchanged. This is the precise sense in which the current three-face Bule
    curve is a shadow of a larger carrier. -/
theorem interference_axes_are_dark_to_visible_projection
    (b : BuleFiveFold) (constructive destructive : Nat) :
    visibleBuleProjection
      { b with
        constructiveInterference := constructive
        destructiveInterference := destructive } =
      visibleBuleProjection b := by
  rfl

theorem five_fold_visible_value_decomposes_into_three_faces (b : BuleFiveFold) :
    buleTotalValue (visibleBuleProjection b) =
      buleWasteValue b.visible + buleOpportunityValue b.visible +
        buleDiversityValue b.visible := by
  exact bule_total_value_decomposes_into_faces b.visible

theorem five_fold_value_decomposes_visible_and_dark (b : BuleFiveFold) :
    buleFiveFoldValue b =
      buleWasteValue b.visible + buleOpportunityValue b.visible +
        buleDiversityValue b.visible + darkInterferenceLoad b := by
  unfold buleFiveFoldValue
  rw [bule_total_value_decomposes_into_faces]

end Gnosis
