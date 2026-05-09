/-
  AffectAxesIndependence.lean
  ===========================

  Why "negative" ≠ "withdraw": a formal decoupling of the hedonic
  valence axis from the motoric tendency axis.

  ## The conflation

  Folk affect theory often collapses the *hedonic* axis
  (positive / negative — feels good vs feels bad) onto the
  *motoric* axis (approach / withdraw / hold — go toward, pull
  away, stay still). The conflation is empirically tempting:
  the population correlation is high (most things you withdraw
  from feel bad, most things you approach feel good), so the two
  labels look interchangeable.

  But the axes are categorically distinct, and they decouple in
  well-attested off-diagonal emotional kinds:

  * **Anger** — negative valence, **approach** tendency: you go
    *toward* the source of threat to confront it.
  * **Relief** — positive valence, **withdraw** tendency: you
    let go, settle back, exhale away from the just-resolved
    pressure.
  * **Anxiety** — negative valence, **hold** tendency: frozen,
    the threat is unlocated so neither approaching nor
    withdrawing discharges the load.
  * **Calm** — positive valence, **hold** tendency: settled, no
    pull either way; the body is at rest with the world.

  Functionally the systems are different. Hedonic valuation
  (does this feel good or bad?) is one circuit. Approach /
  withdraw / hold motor disposition is another. The body-level
  "go vs stop vs freeze" is gated by perceived agency and
  goal-relevance — not by hedonic sign. Folding them together
  loses precisely the off-diagonal information that distinguishes
  anger from sadness, relief from joy, and anxiety from calm.

  This is the same shape of category error as identifying
  body-local trauma with conscious-local rumination because both
  are negatively valenced (cf.
  `LocalizedOverflowConsciousness.valence_not_determined_by_locale`).

  ## What's formalized here

  We mirror the structure of
  `LocalizedOverflowConsciousness.affect_valence_axis_is_independent`
  for the **valence × tendency** plane, plus the joint
  **locale × valence × tendency** triple:

  1. `valence_not_determined_by_tendency` — same tendency,
     different valence (joy and anger both approach).
  2. `tendency_not_determined_by_valence` — same valence,
     different tendency (joy approaches; relief withdraws).
  3. `affect_tendency_axis_is_independent` — the joint
     anti-theorem.
  4. `valence_tendency_grid_fully_inhabited` — the 6-cell form:
     each of the six `(valence, tendency)` cells is non-empty.
  5. `locale_valence_tendency_grid_fully_inhabited` — the strong
     18-cell form: each of the eighteen
     `(locale, valence, tendency)` cells is non-empty, with a named
     `AffectKind` witness from the catalog. This certifies
     triple-axis orthogonality at the matrix-coordinate level.
  6. `locale_valence_tendency_jointly_independent` — pairwise
     independence of all three axes.

  All proofs are by direct witness from the 21-kind `AffectKind`
  catalog. The catalog was extended to cover every cell of the
  18-cell matrix; the inline `reliefVector` is now a backward-
  compatible alias for `affectOfKind .relief`.

  Imports `Gnosis.VibesAsWaveInference`,
  `Gnosis.LocalizedOverflowConsciousness`. Zero `sorry`, zero new
  `axiom`.
-/

import Gnosis.VibesAsWaveInference
import Gnosis.LocalizedOverflowConsciousness

namespace AffectAxesIndependence

open LocalizedOverflowConsciousness (OverflowLocale OverflowValence)
open VibesAsWaveInference
  (AffectVector AffectTendency affectOfKind)

/-! ## Backward-compatible alias for `affectOfKind .relief`

The catalog now contains `.relief` directly (body, positive,
withdraw). `reliefVector` is preserved as an alias so all earlier
proofs and downstream readers keep working without churn. -/

def reliefVector : AffectVector := affectOfKind .relief

theorem relief_is_positive_withdraw :
    reliefVector.emotion.valence = OverflowValence.positive ∧
      reliefVector.tendency = AffectTendency.withdraw := by
  decide

theorem reliefVector_eq_catalog_relief :
    reliefVector = affectOfKind .relief := rfl

/-! ## Anti-theorems: valence and tendency are independent -/

/-- **Same tendency, different valence.** Joy and anger both
    *approach*, yet joy is positively valenced and anger is
    negatively valenced. Approach-coded affect cuts across the
    hedonic axis. -/
theorem valence_not_determined_by_tendency :
    ∃ positiveApproach negativeApproach : AffectVector,
      positiveApproach.tendency = negativeApproach.tendency ∧
      positiveApproach.emotion.valence ≠ negativeApproach.emotion.valence := by
  refine ⟨affectOfKind .joy, affectOfKind .anger, ?_, ?_⟩
  · decide
  · decide

/-- **Same valence, different tendency.** Joy and `reliefVector`
    are both positively valenced, yet joy *approaches* and relief
    *withdraws*. Positive-coded affect cuts across the motoric
    axis. -/
theorem tendency_not_determined_by_valence :
    ∃ positiveApproach positiveWithdraw : AffectVector,
      positiveApproach.emotion.valence = positiveWithdraw.emotion.valence ∧
      positiveApproach.tendency ≠ positiveWithdraw.tendency := by
  refine ⟨affectOfKind .joy, reliefVector, ?_, ?_⟩
  · decide
  · decide

/-- The valence and tendency axes form an independent pair:
    neither determines the other. Symmetric to
    `LocalizedOverflowConsciousness.affect_valence_axis_is_independent`
    on the locale × valence plane. -/
theorem affect_tendency_axis_is_independent :
    (∃ positiveApproach negativeApproach : AffectVector,
      positiveApproach.tendency = negativeApproach.tendency ∧
      positiveApproach.emotion.valence ≠ negativeApproach.emotion.valence) ∧
    (∃ positiveApproach positiveWithdraw : AffectVector,
      positiveApproach.emotion.valence = positiveWithdraw.emotion.valence ∧
      positiveApproach.tendency ≠ positiveWithdraw.tendency) :=
  ⟨valence_not_determined_by_tendency, tendency_not_determined_by_valence⟩

/-! ## Full 2 × 3 cross-axis decoupling

Each of the six `(valence, tendency)` cells is inhabited by a
specific affect kind. This is the strong form of the
independence claim: not "they fail to coincide" but "every joint
configuration has a real emotional witness."
-/

theorem positive_approach_inhabited :
    ∃ a : AffectVector,
      a.emotion.valence = OverflowValence.positive ∧
      a.tendency = AffectTendency.approach := by
  refine ⟨affectOfKind .joy, ?_, ?_⟩
  · decide
  · decide

theorem positive_withdraw_inhabited :
    ∃ a : AffectVector,
      a.emotion.valence = OverflowValence.positive ∧
      a.tendency = AffectTendency.withdraw := by
  refine ⟨reliefVector, ?_, ?_⟩
  · decide
  · decide

theorem positive_hold_inhabited :
    ∃ a : AffectVector,
      a.emotion.valence = OverflowValence.positive ∧
      a.tendency = AffectTendency.hold := by
  refine ⟨affectOfKind .calm, ?_, ?_⟩
  · decide
  · decide

theorem negative_approach_inhabited :
    ∃ a : AffectVector,
      a.emotion.valence = OverflowValence.negative ∧
      a.tendency = AffectTendency.approach := by
  refine ⟨affectOfKind .anger, ?_, ?_⟩
  · decide
  · decide

theorem negative_withdraw_inhabited :
    ∃ a : AffectVector,
      a.emotion.valence = OverflowValence.negative ∧
      a.tendency = AffectTendency.withdraw := by
  refine ⟨affectOfKind .sadness, ?_, ?_⟩
  · decide
  · decide

theorem negative_hold_inhabited :
    ∃ a : AffectVector,
      a.emotion.valence = OverflowValence.negative ∧
      a.tendency = AffectTendency.hold := by
  refine ⟨affectOfKind .anxiety, ?_, ?_⟩
  · decide
  · decide

/-- **Full grid.** All six cells of the valence × tendency grid
    are inhabited. The axes do not collapse onto each other in
    any direction. -/
theorem valence_tendency_grid_fully_inhabited :
    (∃ a : AffectVector,
      a.emotion.valence = OverflowValence.positive ∧
      a.tendency = AffectTendency.approach) ∧
    (∃ a : AffectVector,
      a.emotion.valence = OverflowValence.positive ∧
      a.tendency = AffectTendency.withdraw) ∧
    (∃ a : AffectVector,
      a.emotion.valence = OverflowValence.positive ∧
      a.tendency = AffectTendency.hold) ∧
    (∃ a : AffectVector,
      a.emotion.valence = OverflowValence.negative ∧
      a.tendency = AffectTendency.approach) ∧
    (∃ a : AffectVector,
      a.emotion.valence = OverflowValence.negative ∧
      a.tendency = AffectTendency.withdraw) ∧
    (∃ a : AffectVector,
      a.emotion.valence = OverflowValence.negative ∧
      a.tendency = AffectTendency.hold) :=
  ⟨positive_approach_inhabited,
   positive_withdraw_inhabited,
   positive_hold_inhabited,
   negative_approach_inhabited,
   negative_withdraw_inhabited,
   negative_hold_inhabited⟩

/-! ## Full 3 × 2 × 3 cell-by-cell inhabitation

Every cell of the locale × valence × tendency matrix
(18 cells total) is inhabited by a named `AffectKind` from
the catalog. Each lemma below pins exactly one cell and provides
the witness; the aggregate theorem
`locale_valence_tendency_grid_fully_inhabited` certifies the
catalog as fully populated at matrix-coordinate granularity.

The off-diagonal cells (positive-withdraw, negative-approach,
positive-hold-conscious, negative-hold-environment, etc.) are
exactly the ones folk affect theory tends to collapse — explicit
witnesses are the formal counter to that collapse.
-/

/-! ### body × {positive, negative} × {approach, withdraw, hold} -/

theorem body_positive_approach_inhabited :
    ∃ a : AffectVector,
      a.emotion.locale = OverflowLocale.body ∧
      a.emotion.valence = OverflowValence.positive ∧
      a.tendency = AffectTendency.approach :=
  ⟨affectOfKind .desire, by decide, by decide, by decide⟩

theorem body_positive_withdraw_inhabited :
    ∃ a : AffectVector,
      a.emotion.locale = OverflowLocale.body ∧
      a.emotion.valence = OverflowValence.positive ∧
      a.tendency = AffectTendency.withdraw :=
  ⟨affectOfKind .relief, by decide, by decide, by decide⟩

theorem body_positive_hold_inhabited :
    ∃ a : AffectVector,
      a.emotion.locale = OverflowLocale.body ∧
      a.emotion.valence = OverflowValence.positive ∧
      a.tendency = AffectTendency.hold :=
  ⟨affectOfKind .calm, by decide, by decide, by decide⟩

theorem body_negative_approach_inhabited :
    ∃ a : AffectVector,
      a.emotion.locale = OverflowLocale.body ∧
      a.emotion.valence = OverflowValence.negative ∧
      a.tendency = AffectTendency.approach :=
  ⟨affectOfKind .anger, by decide, by decide, by decide⟩

theorem body_negative_withdraw_inhabited :
    ∃ a : AffectVector,
      a.emotion.locale = OverflowLocale.body ∧
      a.emotion.valence = OverflowValence.negative ∧
      a.tendency = AffectTendency.withdraw :=
  ⟨affectOfKind .fear, by decide, by decide, by decide⟩

theorem body_negative_hold_inhabited :
    ∃ a : AffectVector,
      a.emotion.locale = OverflowLocale.body ∧
      a.emotion.valence = OverflowValence.negative ∧
      a.tendency = AffectTendency.hold :=
  ⟨affectOfKind .numbness, by decide, by decide, by decide⟩

/-! ### conscious × {positive, negative} × {approach, withdraw, hold} -/

theorem conscious_positive_approach_inhabited :
    ∃ a : AffectVector,
      a.emotion.locale = OverflowLocale.conscious ∧
      a.emotion.valence = OverflowValence.positive ∧
      a.tendency = AffectTendency.approach :=
  ⟨affectOfKind .hope, by decide, by decide, by decide⟩

theorem conscious_positive_withdraw_inhabited :
    ∃ a : AffectVector,
      a.emotion.locale = OverflowLocale.conscious ∧
      a.emotion.valence = OverflowValence.positive ∧
      a.tendency = AffectTendency.withdraw :=
  ⟨affectOfKind .nostalgia, by decide, by decide, by decide⟩

theorem conscious_positive_hold_inhabited :
    ∃ a : AffectVector,
      a.emotion.locale = OverflowLocale.conscious ∧
      a.emotion.valence = OverflowValence.positive ∧
      a.tendency = AffectTendency.hold :=
  ⟨affectOfKind .serenity, by decide, by decide, by decide⟩

theorem conscious_negative_approach_inhabited :
    ∃ a : AffectVector,
      a.emotion.locale = OverflowLocale.conscious ∧
      a.emotion.valence = OverflowValence.negative ∧
      a.tendency = AffectTendency.approach :=
  ⟨affectOfKind .resentment, by decide, by decide, by decide⟩

theorem conscious_negative_withdraw_inhabited :
    ∃ a : AffectVector,
      a.emotion.locale = OverflowLocale.conscious ∧
      a.emotion.valence = OverflowValence.negative ∧
      a.tendency = AffectTendency.withdraw :=
  ⟨affectOfKind .sadness, by decide, by decide, by decide⟩

theorem conscious_negative_hold_inhabited :
    ∃ a : AffectVector,
      a.emotion.locale = OverflowLocale.conscious ∧
      a.emotion.valence = OverflowValence.negative ∧
      a.tendency = AffectTendency.hold :=
  ⟨affectOfKind .anxiety, by decide, by decide, by decide⟩

/-! ### environment × {positive, negative} × {approach, withdraw, hold} -/

theorem environment_positive_approach_inhabited :
    ∃ a : AffectVector,
      a.emotion.locale = OverflowLocale.environment ∧
      a.emotion.valence = OverflowValence.positive ∧
      a.tendency = AffectTendency.approach :=
  ⟨affectOfKind .joy, by decide, by decide, by decide⟩

theorem environment_positive_withdraw_inhabited :
    ∃ a : AffectVector,
      a.emotion.locale = OverflowLocale.environment ∧
      a.emotion.valence = OverflowValence.positive ∧
      a.tendency = AffectTendency.withdraw :=
  ⟨affectOfKind .contentment, by decide, by decide, by decide⟩

theorem environment_positive_hold_inhabited :
    ∃ a : AffectVector,
      a.emotion.locale = OverflowLocale.environment ∧
      a.emotion.valence = OverflowValence.positive ∧
      a.tendency = AffectTendency.hold :=
  ⟨affectOfKind .awe, by decide, by decide, by decide⟩

theorem environment_negative_approach_inhabited :
    ∃ a : AffectVector,
      a.emotion.locale = OverflowLocale.environment ∧
      a.emotion.valence = OverflowValence.negative ∧
      a.tendency = AffectTendency.approach :=
  ⟨affectOfKind .outrage, by decide, by decide, by decide⟩

theorem environment_negative_withdraw_inhabited :
    ∃ a : AffectVector,
      a.emotion.locale = OverflowLocale.environment ∧
      a.emotion.valence = OverflowValence.negative ∧
      a.tendency = AffectTendency.withdraw :=
  ⟨affectOfKind .alienation, by decide, by decide, by decide⟩

theorem environment_negative_hold_inhabited :
    ∃ a : AffectVector,
      a.emotion.locale = OverflowLocale.environment ∧
      a.emotion.valence = OverflowValence.negative ∧
      a.tendency = AffectTendency.hold :=
  ⟨affectOfKind .dread, by decide, by decide, by decide⟩

/-! ### Aggregate: all 18 cells inhabited -/

/-- Predicate form of "the cell `(loc, val, tend)` is inhabited by
    some `AffectVector`." Lets us write the 18-fold conjunction
    uniformly. -/
def CellInhabited
    (loc : OverflowLocale) (val : OverflowValence)
    (tend : AffectTendency) : Prop :=
  ∃ a : AffectVector,
    a.emotion.locale = loc ∧
    a.emotion.valence = val ∧
    a.tendency = tend

/-- **Full 18-cell grid.** Every cell of the
    `locale × valence × tendency` matrix (3 × 2 × 3 = 18) is
    inhabited by a named `AffectKind` from the catalog. The three
    axes are genuinely orthogonal coordinates: no off-diagonal
    cell is structurally empty. -/
theorem locale_valence_tendency_grid_fully_inhabited :
    -- body row (positive then negative; approach / withdraw / hold)
    CellInhabited .body .positive .approach ∧
    CellInhabited .body .positive .withdraw ∧
    CellInhabited .body .positive .hold ∧
    CellInhabited .body .negative .approach ∧
    CellInhabited .body .negative .withdraw ∧
    CellInhabited .body .negative .hold ∧
    -- conscious row
    CellInhabited .conscious .positive .approach ∧
    CellInhabited .conscious .positive .withdraw ∧
    CellInhabited .conscious .positive .hold ∧
    CellInhabited .conscious .negative .approach ∧
    CellInhabited .conscious .negative .withdraw ∧
    CellInhabited .conscious .negative .hold ∧
    -- environment row
    CellInhabited .environment .positive .approach ∧
    CellInhabited .environment .positive .withdraw ∧
    CellInhabited .environment .positive .hold ∧
    CellInhabited .environment .negative .approach ∧
    CellInhabited .environment .negative .withdraw ∧
    CellInhabited .environment .negative .hold :=
  ⟨body_positive_approach_inhabited,
   body_positive_withdraw_inhabited,
   body_positive_hold_inhabited,
   body_negative_approach_inhabited,
   body_negative_withdraw_inhabited,
   body_negative_hold_inhabited,
   conscious_positive_approach_inhabited,
   conscious_positive_withdraw_inhabited,
   conscious_positive_hold_inhabited,
   conscious_negative_approach_inhabited,
   conscious_negative_withdraw_inhabited,
   conscious_negative_hold_inhabited,
   environment_positive_approach_inhabited,
   environment_positive_withdraw_inhabited,
   environment_positive_hold_inhabited,
   environment_negative_approach_inhabited,
   environment_negative_withdraw_inhabited,
   environment_negative_hold_inhabited⟩

/-! ## Locale × valence × tendency triple — pairwise independence

A negative-valenced affect can be body-local *and* approach
(anger), conscious-local *and* hold (anxiety), or body-local
*and* withdraw (fear / grief). The triple decoupling certifies
that the three axes are genuinely orthogonal coordinates of an
emotional matrix, not nested labels of one underlying scale.

This is the *pairwise* form of the orthogonality claim. The
*cell-by-cell* form is `locale_valence_tendency_grid_fully_inhabited`
above, which is strictly stronger: pairwise independence permits
some triple cells to be empty, but the 18-cell grid certifies
each triple is realized.
-/

theorem locale_valence_tendency_jointly_independent :
    (∃ a b : AffectVector,
      a.emotion.locale = b.emotion.locale ∧
      a.emotion.valence = b.emotion.valence ∧
      a.tendency ≠ b.tendency) ∧
    (∃ a b : AffectVector,
      a.emotion.valence = b.emotion.valence ∧
      a.tendency = b.tendency ∧
      a.emotion.locale ≠ b.emotion.locale) := by
  refine ⟨?_, ?_⟩
  · refine ⟨affectOfKind .anger, affectOfKind .fear, ?_, ?_, ?_⟩
    · decide
    · decide
    · decide
  · refine ⟨affectOfKind .fear, affectOfKind .sadness, ?_, ?_, ?_⟩
    · decide
    · decide
    · decide

/-! ## Honesty note

The conflation between "negative" and "withdraw" is empirically
tempting because the off-diagonal cells (positive-withdraw,
negative-approach) are population-rarer than the on-diagonal
cells (positive-approach, negative-withdraw). That is a
*frequency* observation, not a *structural* one. The structural
claim — that the two axes are independent coordinates — is what
`affect_tendency_axis_is_independent`,
`valence_tendency_grid_fully_inhabited`, and
`locale_valence_tendency_grid_fully_inhabited` certify.

Treating "negative" as a synonym for "withdraw" makes the same
category error as treating "body-local" as a synonym for
"negative": it folds a real multi-axis structure onto a single
label and loses the off-diagonal information that distinguishes
anger from sadness, relief from joy, and anxiety from calm.

The 21-kind catalog used here is calibrated to *fully inhabit* the
18-cell matrix, not to exhaustively enumerate emotional life.
Multiple kinds map to the same cell (sadness and shame both
conscious-negative-withdraw; joy and love both
environment-positive-approach; fear and grief both
body-negative-withdraw) — that within-cell richness is real, and
no claim of single-kind cell-uniqueness is made. The claim is the
weaker, more honest one: every cell of the matrix has at least one
named witness in the catalog, so the matrix coordinates are not
collapsing onto each other anywhere.

A future extension that adds new affect kinds should preserve the
18-cell coverage. A future extension that adds a fourth axis
(time, social-context, agency, or the like) would generate a new
inhabitation theorem at the next level. The shape of the proof
generalizes; the witnesses are the work.
-/

end AffectAxesIndependence
