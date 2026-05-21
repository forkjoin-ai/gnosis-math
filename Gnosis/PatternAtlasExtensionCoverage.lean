import Gnosis.PatternAtlasExtensions

/-
  PatternAtlasExtensionCoverage.lean
  ==================================

  Burns down the next-exploration target from
  `PatternAtlasExtensions`: a closed finite row list whose entries are
  all theorem-backed.

  Imports `Gnosis.PatternAtlasExtensions`. Zero `sorry`, zero new
  `axiom`.
-/

namespace PatternAtlasExtensionCoverage

open PatternAtlasExtensions

def extensionRows : List ExtensionRow :=
  [.comtePositiveEmpirics, .affectTemporalAxis, .whyFiveWaveBijection]

def rowCovered (row : ExtensionRow) : Bool :=
  extensionRows.contains row

theorem listed_rows_are_theorem_backed :
    ∀ row : ExtensionRow, rowCovered row = true → RowBackedByTheorem row := by
  intro row h
  cases row <;>
    first
    | exact comte_positive_empirics_row_backed
    | exact affect_temporal_axis_row_backed
    | exact why_five_wave_bijection_row_backed

theorem all_extension_rows_covered :
    rowCovered .comtePositiveEmpirics = true ∧
    rowCovered .affectTemporalAxis = true ∧
    rowCovered .whyFiveWaveBijection = true := by
  decide

theorem extension_coverage_witness :
    (∀ row : ExtensionRow, rowCovered row = true → RowBackedByTheorem row) ∧
    rowCovered .comtePositiveEmpirics = true ∧
    rowCovered .affectTemporalAxis = true ∧
    rowCovered .whyFiveWaveBijection = true := by
  exact ⟨listed_rows_are_theorem_backed,
    all_extension_rows_covered.1,
    all_extension_rows_covered.2.1,
    all_extension_rows_covered.2.2⟩

/-! ## Next exploration

Closed by `Gnosis.PatternAtlasExtensionExhaustive`: every current
`ExtensionRow` constructor is covered by the closed list.
-/

end PatternAtlasExtensionCoverage
