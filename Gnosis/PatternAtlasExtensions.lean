import Gnosis.PatternAtlas
import Gnosis.ComtePositiveEmpirics
import Gnosis.AffectMatrixTemporalAxis
import Gnosis.WhyFiveFromWavesBijection

/-
  PatternAtlasExtensions.lean
  ===========================

  Burns down the `PatternAtlas` next-exploration note with rows backed
  by fresh theorem-level modules from this pass.

  Zero `sorry`, zero new `axiom`.
-/

namespace PatternAtlasExtensions

/-- Fresh rows that extend the atlas only because each named module
    now provides an actual theorem-level witness. -/
inductive ExtensionRow where
  | comtePositiveEmpirics
  | affectTemporalAxis
  | whyFiveWaveBijection
  deriving DecidableEq, Repr

/-- Each row is backed by a concrete theorem from its source module. -/
def RowBackedByTheorem : ExtensionRow → Prop
  | .comtePositiveEmpirics =>
      Gnosis.ComtePositiveEmpirics.Auditable
        Gnosis.ComtePositiveEmpirics.canonicalObservationSurface
  | .affectTemporalAxis =>
      AffectMatrixTemporalAxis.gridProjection AffectMatrixTemporalAxis.fastJoy =
        AffectMatrixTemporalAxis.gridProjection AffectMatrixTemporalAxis.slowJoy ∧
      AffectMatrixTemporalAxis.temporalProjection AffectMatrixTemporalAxis.fastJoy ≠
        AffectMatrixTemporalAxis.temporalProjection AffectMatrixTemporalAxis.slowJoy
  | .whyFiveWaveBijection =>
      (∀ m : WhyFiveFromWaves.WaveMode,
        WhyFiveFromWavesBijection.fiveToWaveMode
          (WhyFiveFromWavesBijection.waveModeToFive m) = m) ∧
      (∀ f : TheFiveIsOne.TheFive,
        WhyFiveFromWavesBijection.waveModeToFive
          (WhyFiveFromWavesBijection.fiveToWaveMode f) = f)

theorem comte_positive_empirics_row_backed :
    RowBackedByTheorem .comtePositiveEmpirics :=
  Gnosis.ComtePositiveEmpirics.canonical_observation_surface_auditable

theorem affect_temporal_axis_row_backed :
    RowBackedByTheorem .affectTemporalAxis :=
  AffectMatrixTemporalAxis.tempo_faithful_projection_restores_distinction

theorem why_five_wave_bijection_row_backed :
    RowBackedByTheorem .whyFiveWaveBijection :=
  WhyFiveFromWavesBijection.wave_mode_thefive_bijection

theorem pattern_atlas_extensions_are_theorem_backed :
    RowBackedByTheorem .comtePositiveEmpirics ∧
    RowBackedByTheorem .affectTemporalAxis ∧
    RowBackedByTheorem .whyFiveWaveBijection :=
  ⟨comte_positive_empirics_row_backed,
   affect_temporal_axis_row_backed,
   why_five_wave_bijection_row_backed⟩

/-! ## Next exploration

Closed by `Gnosis.PatternAtlasExtensionCoverage`: extension rows now
have a finite theorem-backed coverage surface.
-/

end PatternAtlasExtensions
