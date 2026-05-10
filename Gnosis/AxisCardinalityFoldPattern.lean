/-
  AxisCardinalityFoldPattern.lean
  =================================

  **Pattern C (cross-pollination):** theorem-level unification for
  *cell-count growth as a combinatorial fold* — the multiplicative
  `List.foldl` over a catalog of finite-axis sizes. This factors the
  same arithmetic spine used in `Gnosis.AffectMatrixAgencyAxis` so it
  applies to any coordinate catalog (affect matrices, social-context
  axes, future topology catalogs, generic grid expansion).

  ## What we prove

  * `axisCells : List Nat → Nat` as the multiplicative fold.
  * Base identities: empty catalog `1`, singleton `k`, append-axis
    `× k`, append-list multiplicativity.
  * **Bridge:** definitional agreement with
    `AffectMatrixAgencyAxis.gridCells`, hence the concrete affect
    cardinality table as one-line corollaries.

  ## Honesty note (scope boundary)

  This module proves **combinatorial coordinate growth** from a
  user-supplied list of axis sizes: the product semantics of counting
  independent finite coordinates. It does **not** prove that the list
  matches `Fintype.card` instances, that every tuple labels a
  empirically distinct state, or any runtime cardinality correctness
  beyond the fold — same epistemic boundary as
  `AffectMatrixAgencyAxis`.

  Imports `Gnosis.AffectMatrixAgencyAxis` only for the `rfl` bridge and
  factored corollaries. Zero `sorry`, zero new `axiom`.
-/

import Gnosis.AffectMatrixAgencyAxis

namespace AxisCardinalityFoldPattern

/-! ## Generic fold -/

/-- Size of a finite-axis coordinate grid as the multiplicative fold
    of axis cardinalities (one `Nat` per axis, in order). -/
def axisCells (cardinalities : List Nat) : Nat :=
  cardinalities.foldl (· * ·) 1

/-! ## Base and structural identities -/

@[simp]
theorem axisCells_nil : axisCells [] = 1 :=
  rfl

/-- Left-multiplying the initial accumulator factors out of a
    multiplicative `foldl`. -/
theorem foldl_mul_left (xs : List Nat) (n : Nat) :
    xs.foldl (· * ·) n = n * xs.foldl (· * ·) 1 := by
  induction xs generalizing n with
  | nil =>
    simp [Nat.mul_one]
  | cons x xs ih =>
    simp only [List.foldl]
    rw [Nat.one_mul x]
    rw [ih (n * x), ih x]
    rw [← Nat.mul_assoc]

theorem foldl_mul_axisCells (xs : List Nat) (n : Nat) :
    xs.foldl (· * ·) n = n * axisCells xs := by
  unfold axisCells
  exact foldl_mul_left xs n

theorem axisCells_cons (x : Nat) (xs : List Nat) :
    axisCells (x :: xs) = x * axisCells xs := by
  unfold axisCells
  simp only [List.foldl, Nat.one_mul]
  exact foldl_mul_left xs x

theorem axisCells_singleton (k : Nat) : axisCells [k] = k := by
  simp [axisCells, List.foldl]

/-- Appending two axis-cardinality lists multiplies the grid sizes. -/
theorem axisCells_append (xs ys : List Nat) :
    axisCells (xs ++ ys) = axisCells xs * axisCells ys := by
  unfold axisCells
  rw [List.foldl_append]
  rw [foldl_mul_left ys (xs.foldl (· * ·) 1)]

/-- **Append-axis step:** extending the catalog by one axis of size
    `k` multiplies the cell count by `k`. -/
theorem axisCells_append_singleton (xs : List Nat) (k : Nat) :
    axisCells (xs ++ [k]) = axisCells xs * k := by
  rw [axisCells_append]
  simp [axisCells_singleton]

/-! ## Bridge to the affect-matrix spine -/

/-- The generic fold agrees definitionally with the affect-matrix
    module's `gridCells`. -/
theorem axisCells_eq_affect_matrix_gridCells (xs : List Nat) :
    axisCells xs = AffectMatrixAgencyAxis.gridCells xs :=
  rfl

/-! ## Affect cardinality table as corollaries -/

theorem three_axis_grid_cells : axisCells [3, 2, 3] = 18 := by
  simpa [axisCells_eq_affect_matrix_gridCells] using
    AffectMatrixAgencyAxis.three_axis_grid_cells

theorem four_axis_grid_cells : axisCells [3, 2, 3, 3] = 54 := by
  simpa [axisCells_eq_affect_matrix_gridCells] using
    AffectMatrixAgencyAxis.four_axis_grid_cells

theorem five_axis_grid_cells : axisCells [3, 2, 3, 3, 3] = 162 := by
  simpa [axisCells_eq_affect_matrix_gridCells] using
    AffectMatrixAgencyAxis.five_axis_grid_cells

theorem six_axis_grid_cells : axisCells [3, 2, 3, 3, 3, 3] = 486 := by
  simpa [axisCells_eq_affect_matrix_gridCells] using
    AffectMatrixAgencyAxis.six_axis_grid_cells

theorem seven_axis_grid_cells : axisCells [3, 2, 3, 3, 3, 3, 3] = 1458 := by
  simpa [axisCells_eq_affect_matrix_gridCells] using
    AffectMatrixAgencyAxis.seven_axis_grid_cells

/-- The affect module's structural lemma factors through
    `axisCells_append_singleton`. -/
theorem affect_axis_extension_factors (cards : List Nat) (k : Nat) :
    AffectMatrixAgencyAxis.gridCells (cards ++ [k]) =
      AffectMatrixAgencyAxis.gridCells cards * k :=
  AffectMatrixAgencyAxis.axis_extension_multiplies_cells cards k

theorem axisCells_append_singleton_eq_affect (xs : List Nat) (k : Nat) :
    axisCells (xs ++ [k]) = AffectMatrixAgencyAxis.gridCells xs * k := by
  rw [axisCells_eq_affect_matrix_gridCells]
  exact AffectMatrixAgencyAxis.axis_extension_multiplies_cells xs k

/-! ## Bundled headline witness -/

/-- Single statement bundling the generic fold laws, append
    multiplicativity, agreement with `AffectMatrixAgencyAxis.gridCells`,
    the concrete affect cardinality ladder, and the append-axis law. -/
theorem axis_cardinality_fold_pattern_witness :
    (axisCells [] = 1) ∧
    (∀ k : Nat, axisCells [k] = k) ∧
    (∀ xs ys : List Nat,
      axisCells (xs ++ ys) = axisCells xs * axisCells ys) ∧
    (∀ xs : List Nat, ∀ k : Nat,
      axisCells (xs ++ [k]) = axisCells xs * k) ∧
    (∀ xs : List Nat, axisCells xs = AffectMatrixAgencyAxis.gridCells xs) ∧
    (axisCells [3, 2, 3] = 18) ∧
    (axisCells [3, 2, 3, 3] = 54) ∧
    (axisCells [3, 2, 3, 3, 3] = 162) ∧
    (axisCells [3, 2, 3, 3, 3, 3] = 486) ∧
    (axisCells [3, 2, 3, 3, 3, 3, 3] = 1458) ∧
    (∀ cards : List Nat, ∀ k : Nat,
      AffectMatrixAgencyAxis.gridCells (cards ++ [k]) =
        AffectMatrixAgencyAxis.gridCells cards * k) :=
  ⟨axisCells_nil,
   axisCells_singleton,
   axisCells_append,
   axisCells_append_singleton,
   axisCells_eq_affect_matrix_gridCells,
   three_axis_grid_cells,
   four_axis_grid_cells,
   five_axis_grid_cells,
   six_axis_grid_cells,
   seven_axis_grid_cells,
   AffectMatrixAgencyAxis.axis_extension_multiplies_cells⟩

end AxisCardinalityFoldPattern
