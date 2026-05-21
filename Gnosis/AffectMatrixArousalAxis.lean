import Gnosis.AffectMatrixTemporalAxis

/-
  AffectMatrixArousalAxis.lean
  ============================

  Burns down the next-exploration target from
  `AffectMatrixTemporalAxis`: a finite arousal axis is projected away
  by the 18-cell grid but restored by a faithful coordinate product.

  Imports `Gnosis.AffectMatrixTemporalAxis`. Zero `sorry`, zero new
  `axiom`.
-/

namespace AffectMatrixArousalAxis

open AffectMatrixCompleteness (PhaseSnapshot)
open AffectMatrixTemporalAxis (gridProjection)

inductive Arousal where
  | low
  | medium
  | high
  deriving DecidableEq, Repr

structure ArousalPhenomenon where
  name     : String
  snapshot : PhaseSnapshot
  arousal  : Arousal
  deriving Repr

def arousalGridProjection (p : ArousalPhenomenon) : PhaseSnapshot :=
  p.snapshot

def arousalFaithfulProjection (p : ArousalPhenomenon) : PhaseSnapshot × Arousal :=
  (p.snapshot, p.arousal)

def lowAwe : ArousalPhenomenon :=
  { name := "low-awe"
    snapshot := { locale := .conscious, valence := .positive, tendency := .approach }
    arousal := .low }

def highAwe : ArousalPhenomenon :=
  { name := "high-awe"
    snapshot := { locale := .conscious, valence := .positive, tendency := .approach }
    arousal := .high }

theorem low_and_high_arousal_same_grid_projection :
    arousalGridProjection lowAwe = arousalGridProjection highAwe := by
  rfl

theorem low_and_high_arousal_distinct :
    lowAwe.arousal ≠ highAwe.arousal := by
  decide

theorem arousal_projection_distinguishes_low_and_high :
    arousalFaithfulProjection lowAwe ≠ arousalFaithfulProjection highAwe := by
  intro h
  exact low_and_high_arousal_distinct (Prod.mk.inj h).2

theorem arousal_axis_is_projected_away_and_restored :
    arousalGridProjection lowAwe = arousalGridProjection highAwe ∧
    arousalFaithfulProjection lowAwe ≠ arousalFaithfulProjection highAwe := by
  exact ⟨low_and_high_arousal_same_grid_projection,
    arousal_projection_distinguishes_low_and_high⟩

/-! ## Next exploration

Closed by `Gnosis.AffectMatrixTemporalArousalProduct`: tempo and
arousal are now combined in one product axis and independently
forgotten by the base grid projection.
-/

end AffectMatrixArousalAxis
