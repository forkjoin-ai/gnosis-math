import Gnosis.PatternAtlasExtensionCoverage

/-
  PatternAtlasExtensionExhaustive.lean
  ====================================

  Burns down the next-exploration target from
  `PatternAtlasExtensionCoverage`: every constructor of `ExtensionRow`
  is present in the closed coverage list.

  Imports `Gnosis.PatternAtlasExtensionCoverage`. Zero `sorry`, zero
  new `axiom`.
-/

namespace PatternAtlasExtensionExhaustive

open PatternAtlasExtensions
open PatternAtlasExtensionCoverage

theorem every_extension_row_covered (row : ExtensionRow) :
    rowCovered row = true := by
  cases row <;> decide

theorem every_extension_row_theorem_backed (row : ExtensionRow) :
    RowBackedByTheorem row :=
  listed_rows_are_theorem_backed row (every_extension_row_covered row)

theorem exhaustive_extension_coverage_witness :
    (∀ row : ExtensionRow, rowCovered row = true) ∧
    (∀ row : ExtensionRow, RowBackedByTheorem row) :=
  ⟨every_extension_row_covered, every_extension_row_theorem_backed⟩

/-! ## Next exploration

The finite atlas-extension audit chain is closed for the current
`ExtensionRow` constructors. The next honest extension is to add a new
row only when a fresh theorem-level module supplies a real witness.
-/

end PatternAtlasExtensionExhaustive
