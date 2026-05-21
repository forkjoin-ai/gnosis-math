import Gnosis.AffectMatrixArousalAxis

/-
  AffectMatrixTemporalArousalProduct.lean
  =======================================

  Burns down the next-exploration target from
  `AffectMatrixArousalAxis`: tempo and arousal form an independent
  product extension whose extra coordinates are both forgotten by the
  legacy grid projection.

  Imports `Gnosis.AffectMatrixArousalAxis`. Zero `sorry`, zero new
  `axiom`.
-/

namespace AffectMatrixTemporalArousalProduct

open AffectMatrixCompleteness (PhaseSnapshot)
open AffectMatrixArousalAxis (Arousal)

structure TemporalArousalPhenomenon where
  name     : String
  snapshot : PhaseSnapshot
  tempo    : Nat
  arousal  : Arousal
  deriving Repr

def gridProjection (p : TemporalArousalPhenomenon) : PhaseSnapshot :=
  p.snapshot

def faithfulProjection (p : TemporalArousalPhenomenon) :
    PhaseSnapshot × Nat × Arousal :=
  (p.snapshot, p.tempo, p.arousal)

def quickLowJoy : TemporalArousalPhenomenon :=
  { name := "quick-low-joy"
    snapshot := { locale := .conscious, valence := .positive, tendency := .approach }
    tempo := 1
    arousal := .low }

def slowHighJoy : TemporalArousalPhenomenon :=
  { name := "slow-high-joy"
    snapshot := { locale := .conscious, valence := .positive, tendency := .approach }
    tempo := 8
    arousal := .high }

theorem product_axes_same_grid_projection :
    gridProjection quickLowJoy = gridProjection slowHighJoy := by
  rfl

theorem product_axes_distinct_tempo :
    quickLowJoy.tempo ≠ slowHighJoy.tempo := by
  decide

theorem product_axes_distinct_arousal :
    quickLowJoy.arousal ≠ slowHighJoy.arousal := by
  decide

theorem product_projection_distinguishes_axes :
    faithfulProjection quickLowJoy ≠ faithfulProjection slowHighJoy := by
  intro h
  exact product_axes_distinct_arousal (Prod.mk.inj (Prod.mk.inj h).2).2

theorem temporal_arousal_product_is_projected_away_and_restored :
    gridProjection quickLowJoy = gridProjection slowHighJoy ∧
    quickLowJoy.tempo ≠ slowHighJoy.tempo ∧
    quickLowJoy.arousal ≠ slowHighJoy.arousal ∧
    faithfulProjection quickLowJoy ≠ faithfulProjection slowHighJoy := by
  exact ⟨product_axes_same_grid_projection,
    product_axes_distinct_tempo,
    product_axes_distinct_arousal,
    product_projection_distinguishes_axes⟩

/-! ## Next exploration

The finite affect-axis projection chain is closed for tempo and arousal.
The next honest extension is empirical axis selection, not another
formal product proof.
-/

end AffectMatrixTemporalArousalProduct
