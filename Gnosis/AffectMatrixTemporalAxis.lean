import Gnosis.AffectMatrixCompleteness

/-
  AffectMatrixTemporalAxis.lean
  =============================

  Burns down the next-exploration target from
  `AffectMatrixCompleteness`: tempo is a real representational axis,
  and the 18-cell grid projects it away.

  Imports `Gnosis.AffectMatrixCompleteness`. Zero `sorry`, zero new
  `axiom`.
-/

namespace AffectMatrixTemporalAxis

open LocalizedOverflowConsciousness (OverflowLocale OverflowValence)
open VibesAsWaveInference (AffectTendency)
open AffectMatrixCompleteness (PhaseSnapshot)

/-- A single-phase phenomenon with an explicit duration/tempo field. -/
structure TemporalPhenomenon where
  name     : String
  snapshot : PhaseSnapshot
  tempo    : Nat
  deriving Repr

/-- The legacy 18-cell projection forgets tempo. -/
def gridProjection (p : TemporalPhenomenon) : PhaseSnapshot :=
  p.snapshot

/-- A tempo-faithful projection keeps the grid coordinates plus tempo. -/
def temporalProjection (p : TemporalPhenomenon) : PhaseSnapshot × Nat :=
  (p.snapshot, p.tempo)

def fastJoy : TemporalPhenomenon :=
  { name := "fast-joy"
    snapshot := { locale := .conscious, valence := .positive, tendency := .approach }
    tempo := 1 }

def slowJoy : TemporalPhenomenon :=
  { name := "slow-joy"
    snapshot := { locale := .conscious, valence := .positive, tendency := .approach }
    tempo := 8 }

theorem fast_and_slow_joy_same_grid_projection :
    gridProjection fastJoy = gridProjection slowJoy := by
  rfl

theorem fast_and_slow_joy_distinct_tempo :
    fastJoy.tempo ≠ slowJoy.tempo := by
  decide

/-- Same 18-cell grid coordinate, different tempo: the grid cannot
    distinguish the two values without an added temporal axis. -/
theorem tempo_axis_is_projected_away :
    gridProjection fastJoy = gridProjection slowJoy ∧
    fastJoy.tempo ≠ slowJoy.tempo := by
  exact ⟨fast_and_slow_joy_same_grid_projection, fast_and_slow_joy_distinct_tempo⟩

theorem temporal_projection_distinguishes_fast_and_slow_joy :
    temporalProjection fastJoy ≠ temporalProjection slowJoy := by
  intro h
  exact fast_and_slow_joy_distinct_tempo (Prod.mk.inj h).2

/-- Adding a tempo slot gives the faithful representation the 18-cell
    matrix lacks. -/
theorem tempo_faithful_projection_restores_distinction :
    gridProjection fastJoy = gridProjection slowJoy ∧
    temporalProjection fastJoy ≠ temporalProjection slowJoy := by
  exact ⟨fast_and_slow_joy_same_grid_projection,
    temporal_projection_distinguishes_fast_and_slow_joy⟩

/-! ## Next exploration

Closed by `Gnosis.AffectMatrixArousalAxis`: finite arousal is now
projected away by the 18-cell grid and restored by a faithful product.
-/

end AffectMatrixTemporalAxis
