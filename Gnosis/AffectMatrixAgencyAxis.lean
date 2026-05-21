import Gnosis.AffectMatrixFourthAxis

/-
  AffectMatrixAgencyAxis.lean
  ===========================

  The user observation, escalated to meta-level:

  > Instead of instantiating the same scaling pattern with `Agency`
  > as a fixed type, formalize the meta-scaling lemma making the
  > axis itself a `Type` parameter. A single theorem then covers
  > every possible additional axis with finite cardinality, and
  > cell-count growth becomes a fold over an axis-cardinality list.
  > The empirical instantiation (`Agency := selfCaused | otherCaused
  > | impersonal`) becomes a one-line corollary, and a 6th, 7th, ...
  > axis would each be one-line corollaries too.

  ## What we prove

  1. **Meta-scaling lemma** `cell_inhabited_n_lifts_to_n_plus_one`:
     for *any* base-witness type `Base`, *any* predicate
     `P : Base → Prop` with at least one witness, and *any*
     new-axis type `Axis`, every value `a : Axis` admits a lifted
     witness for `P-and-axis-equals-a`. The axis is a `Type`
     parameter, not a fixed enumeration.
  2. **Empirical 5-axis instantiation** with
     `Agency := { selfCaused, otherCaused, impersonal }`:
     `five_axis_grid_fully_inhabited` is a one-line corollary of the
     meta-lemma applied to the 4-axis coverage from
     `AffectMatrixFourthAxis`.
  3. **Sixth and seventh axes as one-liners.** A temporal-phase axis
     `AffectTime` and a reality-mode axis `Modality` slot in by the
     same one-line application of the meta-lemma. No new per-cell
     witnesses are needed at any level — coverage propagates by
     pure scaffolding.
  4. **Cell-count growth as a fold over axis cardinalities.**
     `gridCells : List Nat → Nat` defined as the multiplicative
     fold; the structural identity `gridCells (cards ++ [k]) =
     gridCells cards * k` is the meta-version of "adding a k-state
     axis multiplies the grid by k."

  ## Honesty note on Rustic counting

  The lift itself does not need a finiteness typeclass: given any
  axis `a : Axis`, the meta-lemma produces a lifted witness.
  Counting enters separately. We model that part with a plain
  `List Nat` of axis cardinalities (one entry per axis) and a
  multiplicative fold, which is faithful to the Rustic Church
  cell-count growth pattern.

  Imports `Gnosis.AffectMatrixFourthAxis` (transitively pulls in
  `LocalizedOverflowConsciousness`, `VibesAsWaveInference`, and
  `AffectAxesIndependence`). Zero `sorry`, zero new `axiom`.
-/


namespace AffectMatrixAgencyAxis

open LocalizedOverflowConsciousness (OverflowLocale OverflowValence)
open VibesAsWaveInference (AffectVector AffectTendency affectOfKind)
open AffectMatrixFourthAxis
  (ContextualAffect SocialContext CellInhabited4
   four_axis_grid_fully_inhabited)

/-! ## The meta-scaling shape

  `NextAxisWitness Base Axis` pairs an existing base witness with
  one value on a new axis. `NextAxisInhabited P a` asserts that
  some such pair satisfies `P` on the base part *and* matches the
  given new-axis value. -/

/-- Generic axis-extending wrapper: pair a base witness with a value
    on the new axis. Empty parameters constraints — the lift works
    for any `Base` and any `Axis`, finite or not. -/
structure NextAxisWitness (Base : Type) (Axis : Type) where
  base : Base
  axis : Axis

/-- The lifted predicate: the base predicate `P` extended by a
    fixed-axis-value conjunct. This is the meta-version of
    `CellInhabited{n+1}`. -/
def NextAxisInhabited
    {Base Axis : Type} (P : Base → Prop) (a : Axis) : Prop :=
  ∃ w : NextAxisWitness Base Axis, P w.base ∧ w.axis = a

/-! ## The meta-scaling lemma

  This is the architectural deliverable: every base-witness lift
  packaged once for all axes. The empirical instantiations below
  reduce to one-line corollaries. -/

/-- **Meta-scaling lemma.** For any base-witness type `Base`, any
    predicate `P : Base → Prop` with at least one base witness, and
    any new-axis type `Axis`, every value `a : Axis` admits a
    lifted witness for `P-and-axis-equals-a`.

    This generalizes
    `AffectMatrixFourthAxis.cell_inhabited_3_lifts_to_4` by making
    the axis itself a `Type` parameter rather than a fixed
    enumeration. -/
theorem cell_inhabited_n_lifts_to_n_plus_one
    {Base Axis : Type} {P : Base → Prop}
    (hBase : ∃ b : Base, P b) (a : Axis) :
    NextAxisInhabited P a := by
  obtain ⟨b, hb⟩ := hBase
  exact ⟨{ base := b, axis := a }, hb, rfl⟩

/-- **Universal-form variant.** When the base predicate is
    universally inhabited over a parameter pack `Q`, the lifted
    predicate is universally inhabited over the same pack and any
    new-axis value. Pure rewrap of the meta-lemma; included to make
    the universal-coverage chaining transparent. -/
theorem cell_inhabited_universal_lifts
    {Q : Type} {Base Axis : Type} {P : Q → Base → Prop}
    (hBase : ∀ q : Q, ∃ b : Base, P q b)
    (q : Q) (a : Axis) :
    NextAxisInhabited (P q) a :=
  cell_inhabited_n_lifts_to_n_plus_one (hBase q) a

/-! ## Empirical instantiation 1: Agency as the 5th axis

  `Agency := { selfCaused, otherCaused, impersonal }` — does the
  emotional cause locate to the self, to another agent, or to no
  agent (impersonal events, weather, accident)? This is a standard
  attribution-theory axis from social psychology. -/

/-- Agency: the locus-of-cause coordinate of an emotional
    experience. -/
inductive Agency where
  | selfCaused
  | otherCaused
  | impersonal
  deriving DecidableEq, Repr

/-- The 5-axis witness: a `ContextualAffect` paired with an
    `Agency` value. -/
abbrev FiveAxisWitness := NextAxisWitness ContextualAffect Agency

/-- Five-axis cell predicate. Defined directly as a
    `NextAxisInhabited` so that the meta-lemma applies in one line. -/
def CellInhabited5
    (l : OverflowLocale) (v : OverflowValence) (t : AffectTendency)
    (c : SocialContext) (g : Agency) : Prop :=
  NextAxisInhabited
    (fun ca : ContextualAffect =>
      ca.affect.emotion.locale = l ∧
      ca.affect.emotion.valence = v ∧
      ca.affect.tendency = t ∧
      ca.social_context = c)
    g

/-- **Five-axis full coverage as a one-line corollary** of
    `cell_inhabited_n_lifts_to_n_plus_one` and
    `four_axis_grid_fully_inhabited`. -/
theorem five_axis_grid_fully_inhabited
    (l : OverflowLocale) (v : OverflowValence) (t : AffectTendency)
    (c : SocialContext) (g : Agency) :
    CellInhabited5 l v t c g :=
  cell_inhabited_n_lifts_to_n_plus_one
    (four_axis_grid_fully_inhabited l v t c) g

/-! ## Empirical instantiation 2: a 6th axis (temporal phase) as
    a one-line corollary

  `AffectTime := { onset, peak, resolution }` — the temporal
  phase of an emotional episode. -/

inductive AffectTime where
  | onset
  | peak
  | resolution
  deriving DecidableEq, Repr

abbrev SixAxisWitness := NextAxisWitness FiveAxisWitness AffectTime

/-- Six-axis cell predicate. The grouping `(4-conjuncts) ∧ axis = g`
    matches the shape that the meta-lemma's lift produces from the
    5-axis predicate, so the corollary lands by definitional
    equality rather than by rebalancing the conjunction. -/
def CellInhabited6
    (l : OverflowLocale) (v : OverflowValence) (t : AffectTendency)
    (c : SocialContext) (g : Agency) (τ : AffectTime) : Prop :=
  NextAxisInhabited
    (fun w : FiveAxisWitness =>
      (w.base.affect.emotion.locale = l ∧
       w.base.affect.emotion.valence = v ∧
       w.base.affect.tendency = t ∧
       w.base.social_context = c) ∧
      w.axis = g)
    τ

/-- **Six-axis full coverage as a one-line corollary** of the
    meta-lemma applied to the 5-axis coverage. -/
theorem six_axis_grid_fully_inhabited
    (l : OverflowLocale) (v : OverflowValence) (t : AffectTendency)
    (c : SocialContext) (g : Agency) (τ : AffectTime) :
    CellInhabited6 l v t c g τ :=
  cell_inhabited_n_lifts_to_n_plus_one
    (five_axis_grid_fully_inhabited l v t c g) τ

/-! ## Empirical instantiation 3: a 7th axis (reality mode) as
    a one-line corollary

  `Modality := { actual, imagined, remembered }` — is the affect
  triggered by an actually present situation, an imagined one, or a
  remembered one? -/

inductive Modality where
  | actual
  | imagined
  | remembered
  deriving DecidableEq, Repr

abbrev SevenAxisWitness := NextAxisWitness SixAxisWitness Modality

/-- Seven-axis cell predicate. The grouping
    `((4-conjuncts) ∧ axis-g) ∧ axis-τ` matches the shape that two
    successive meta-lemma lifts produce. -/
def CellInhabited7
    (l : OverflowLocale) (v : OverflowValence) (t : AffectTendency)
    (c : SocialContext) (g : Agency) (τ : AffectTime)
    (m : Modality) : Prop :=
  NextAxisInhabited
    (fun w : SixAxisWitness =>
      ((w.base.base.affect.emotion.locale = l ∧
        w.base.base.affect.emotion.valence = v ∧
        w.base.base.affect.tendency = t ∧
        w.base.base.social_context = c) ∧
       w.base.axis = g) ∧
      w.axis = τ)
    m

/-- **Seven-axis full coverage as a one-line corollary** of the
    meta-lemma applied to the 6-axis coverage. -/
theorem seven_axis_grid_fully_inhabited
    (l : OverflowLocale) (v : OverflowValence) (t : AffectTendency)
    (c : SocialContext) (g : Agency) (τ : AffectTime)
    (m : Modality) :
    CellInhabited7 l v t c g τ m :=
  cell_inhabited_n_lifts_to_n_plus_one
    (six_axis_grid_fully_inhabited l v t c g τ) m

/-! ## Cell-count growth as a fold over an axis-cardinality list

  Each axis contributes a cardinality `k`; the grid size is the
  product over the list. Adding a new axis with `k` states is the
  scalar multiplication `× k` step on this fold. -/

/-- Total cell count of a multi-axis grid as the multiplicative
    fold of axis cardinalities. -/
def gridCells (cardinalities : List Nat) : Nat :=
  cardinalities.foldl (· * ·) 1

theorem three_axis_grid_cells :
    gridCells [3, 2, 3] = 18 := by decide

theorem four_axis_grid_cells :
    gridCells [3, 2, 3, 3] = 54 := by decide

theorem five_axis_grid_cells :
    gridCells [3, 2, 3, 3, 3] = 162 := by decide

theorem six_axis_grid_cells :
    gridCells [3, 2, 3, 3, 3, 3] = 486 := by decide

theorem seven_axis_grid_cells :
    gridCells [3, 2, 3, 3, 3, 3, 3] = 1458 := by decide

/-- **The structural identity behind every "× k" step.** Adding a
    `k`-state axis to any existing axis-cardinality list multiplies
    the grid size by `k`. This is the cell-count meta-version of
    `cell_inhabited_n_lifts_to_n_plus_one`: the lemma adds a
    coordinate, this multiplies the count. -/
theorem axis_extension_multiplies_cells (cards : List Nat) (k : Nat) :
    gridCells (cards ++ [k]) = gridCells cards * k := by
  show (cards ++ [k]).foldl (· * ·) 1 = cards.foldl (· * ·) 1 * k
  rw [List.foldl_append]
  rfl

/-! ## Sample 5-axis named witnesses

  Three concrete cells of the 5-axis grid, derived from the
  one-line `five_axis_grid_fully_inhabited` corollary. The point of
  these is to demonstrate the per-cell pattern still works at the
  5-axis level without writing any new proof — the architecture
  carries every cell. -/

theorem self_caused_solitary_anger_inhabited :
    CellInhabited5 .conscious .negative .approach .solitary
      .selfCaused :=
  five_axis_grid_fully_inhabited .conscious .negative .approach
    .solitary .selfCaused

theorem other_caused_dyadic_anger_inhabited :
    CellInhabited5 .conscious .negative .approach .dyadic
      .otherCaused :=
  five_axis_grid_fully_inhabited .conscious .negative .approach
    .dyadic .otherCaused

theorem impersonal_environmental_dread_inhabited :
    CellInhabited5 .environment .negative .hold .group
      .impersonal :=
  five_axis_grid_fully_inhabited .environment .negative .hold
    .group .impersonal

/-! ## Independence of the new axis at the 5-axis level

  Two `FiveAxisWitness`es can agree on the four prior coordinates
  but differ on `Agency`. The new axis is genuinely orthogonal at
  the meta-level too. -/

theorem agency_axis_is_independent :
    ∃ w1 w2 : FiveAxisWitness,
      w1.base.affect.emotion.locale = w2.base.affect.emotion.locale ∧
      w1.base.affect.emotion.valence = w2.base.affect.emotion.valence ∧
      w1.base.affect.tendency = w2.base.affect.tendency ∧
      w1.base.social_context = w2.base.social_context ∧
      w1.axis ≠ w2.axis := by
  refine
    ⟨{ base := { affect := affectOfKind .anger,
                 social_context := SocialContext.solitary },
       axis := Agency.selfCaused },
     { base := { affect := affectOfKind .anger,
                 social_context := SocialContext.solitary },
       axis := Agency.otherCaused },
     ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · rfl
  · rfl
  · decide

/-! ## Headline witness

  A single statement that bundles the meta-lemma, all three
  one-line empirical corollaries, the structural cell-count
  identity, and the cardinality table. -/

theorem axis_meta_scaling_witness :
    -- Meta-lemma: any base witness lifts to any axis
    (∀ {Base Axis : Type} {P : Base → Prop},
      (∃ b : Base, P b) → ∀ a : Axis, NextAxisInhabited P a) ∧
    -- 5-, 6-, 7-axis full coverage as one-line corollaries
    (∀ l v t c g, CellInhabited5 l v t c g) ∧
    (∀ l v t c g τ, CellInhabited6 l v t c g τ) ∧
    (∀ l v t c g τ m, CellInhabited7 l v t c g τ m) ∧
    -- Cell-count growth as a fold
    gridCells [3, 2, 3] = 18 ∧
    gridCells [3, 2, 3, 3] = 54 ∧
    gridCells [3, 2, 3, 3, 3] = 162 ∧
    gridCells [3, 2, 3, 3, 3, 3] = 486 ∧
    gridCells [3, 2, 3, 3, 3, 3, 3] = 1458 ∧
    -- Structural × k identity behind every step
    (∀ cards : List Nat, ∀ k : Nat,
      gridCells (cards ++ [k]) = gridCells cards * k) := by
  refine ⟨@cell_inhabited_n_lifts_to_n_plus_one,
          five_axis_grid_fully_inhabited,
          six_axis_grid_fully_inhabited,
          seven_axis_grid_fully_inhabited,
          ?_, ?_, ?_, ?_, ?_,
          axis_extension_multiplies_cells⟩
  · decide
  · decide
  · decide
  · decide
  · decide

/-! ## Honesty note

What we proved:

  * A single meta-lemma `cell_inhabited_n_lifts_to_n_plus_one`
    parameterizes the lift over an arbitrary axis type. The
    "scaffolding generalizes" claim is closed at the meta-level: a
    fixed Lean proof covers every possible additional axis, finite
    or not.
  * Three concrete extensions (5, 6, 7 axes — Agency, AffectTime,
    Modality) are each one-line corollaries of the meta-lemma
    chained off the existing 4-axis coverage. No per-cell
    witnesses, no new induction; pure architectural propagation.
  * Cell-count growth is a single fold `gridCells = foldl (· * ·)
    1` over a list of axis cardinalities, with the structural
    identity `gridCells (cards ++ [k]) = gridCells cards * k`
    proved once.

What we did **not** prove:

  * That the cardinality list really matches the type cardinalities.
    The list is supplied manually, and the burden of correctness is
    on the user to keep it in sync with the axis enumerations.
  * That further axes are *empirically meaningful*. The architecture
    will accept any new `Type` as an axis; that does not mean every
    new axis maps to a real phenomenological coordinate. Picking
    an axis is empirical work; lifting it once chosen is the
    architectural one-liner this module formalizes.
  * That every 5-, 6-, or 7-axis cell labels a phenomenologically
    distinct experience. The cell count grows combinatorially
    (`18 → 54 → 162 → 486 → 1458 → ...`); the structural
    inhabitation is constructive, but the empirical distinctness
    is a separate claim and one this module does not make.

## Next exploration

The Rustic Church boundary keeps this module at the manual
cardinality-list level. Do not route this file to external cardinality
machinery; add a new finite axis only when the local enumeration and
manual count are both updated together.
-/

end AffectMatrixAgencyAxis
