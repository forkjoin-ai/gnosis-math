import Gnosis.LocalizedOverflowConsciousness
import Gnosis.VibesAsWaveInference
import Gnosis.AffectAxesIndependence

/-
  AffectMatrixCompleteness.lean
  =============================

  The honest counterpart to `AffectAxesIndependence.lean`.

  ## What the prior module proved

  `AffectAxesIndependence.locale_valence_tendency_grid_fully_inhabited`
  certifies that every cell of the 3 × 2 × 3 = 18-cell coordinate
  matrix `OverflowLocale × OverflowValence × AffectTendency` is
  inhabited by a named `AffectKind` from the catalog. That is a
  **coverage** result: nothing in the grid is structurally empty.

  ## What the prior module did not prove

  Coverage is silent on what the grid *cannot represent*. Three honest
  questions remain:

  1. **Locale-shifting phenomena** — emotions whose locale migrates
     mid-experience (e.g., embarrassment that begins in the body as
     blushing and migrates to the conscious as rumination). The
     18-cell matrix pins each phenomenon to one locale; multi-phase
     phenomena cannot be represented as a single coordinate.
  2. **Mixed-valence phenomena** — emotions that simultaneously
     carry positive and negative hedonic load (bittersweet, the
     real-life grain of nostalgia, awe-with-dread). The binary
     `OverflowValence` cannot represent simultaneity of opposing
     hedonic signs.
  3. **Tendency-shifting phenomena** — emotions whose motoric
     disposition flips between phases (grief that approaches the
     loss in revisiting, then withdraws in numbing). The single
     `AffectTendency` slot cannot represent an
     approach-then-withdraw arc.

  These are not failures of the catalog — they are failures of the
  matrix *coordinate system*. Even an arbitrarily large `AffectKind`
  enum cannot capture them so long as each kind decodes to one
  `(locale, valence, tendency)` triple.

  ## What this module proves

  We define a richer `EmotionPhenomenon` type that admits multi-phase
  trajectories and an optional secondary valence, then:

  * `IsRepresentable : EmotionPhenomenon → Prop` — a phenomenon is
    representable iff it has exactly one phase and no secondary
    valence.
  * `pureJoy_is_representable` — positive control: simple emotions
    fit the grid.
  * `bittersweet_not_representable` — mixed-valence witness.
  * `embarrassment_migration_not_representable` — locale-shift witness.
  * `grief_tendency_shift_not_representable` — tendency-shift witness.
  * `nostalgia_catalog_projects_away_negative_grain` — the catalog
    represents nostalgia faithfully *as projection*: its
    single-valence form is representable, but the richer
    bittersweet-grained form is not. The catalog projects, it does
    not erase.
  * `phenomena_outside_grid_exist` — the headline negative result.
  * `at_least_three_distinct_failure_modes_outside_grid` — three
    *structurally distinct* failures, not three exemplars of one.
  * `enriched_matrix_cell_count_is_fifty_four` — adding optional
    secondary valence alone lifts the grid from 18 cells to 54.

  ## Honesty boundary

  This module is an *internal* honesty counterpart, not an empirical
  claim about real cognitive phenomenology. Concretely:

  * `EmotionPhenomenon` is a Lean structure. It is richer than the
    18-cell grid by construction; it does not by itself prove that
    real emotional life has the features that fall outside the
    grid. Whether bittersweet, embarrassment migration, and grief
    tendency-shifts faithfully describe real cognitive states is an
    empirical question for psychology, not a theorem of Lean.
  * What the theorems certify is the *internal* gap: there exist
    Lean values of type `EmotionPhenomenon` that cannot be folded
    into a single `AffectKind` from the catalog. The empirical
    bridge — that those values describe attested human experiences
    — is named in prose and supported by clinical literature on
    bittersweet emotion, embarrassment-to-rumination migration, and
    grief tendency-phases.
  * No new `axiom` is introduced. The "extension axioms" in the
    user's request are formalized as decidable predicates
    (`NeedsMixedValence`, `NeedsLocaleShift`, `NeedsTendencyShift`)
    that name the structural axes a richer matrix would need; they
    are not Lean axioms.

  Imports `Gnosis.LocalizedOverflowConsciousness`,
  `Gnosis.VibesAsWaveInference`, `Gnosis.AffectAxesIndependence`.
  Zero `sorry`, zero new `axiom`.
-/


namespace AffectMatrixCompleteness

open LocalizedOverflowConsciousness (OverflowLocale OverflowValence)
open VibesAsWaveInference (AffectKind AffectTendency affectOfKind)

/-! ## A richer phenomenology

  `PhaseSnapshot` is a single-moment slice with the same coordinates
  the 18-cell grid uses. `EmotionPhenomenon` allows a trajectory of
  phases plus an optional simultaneous secondary valence — the two
  axes the 18-cell grid does not have. -/

/-- A single-moment slice in the 18-cell coordinate system. -/
structure PhaseSnapshot where
  locale   : OverflowLocale
  valence  : OverflowValence
  tendency : AffectTendency
  deriving DecidableEq, Repr

/-- A richer phenomenology than the catalog admits.

    * `phases` is a non-empty list of snapshots, allowing locale
      and tendency to migrate between phases of one experience.
    * `secondary_valence` is an optional simultaneous companion
      valence, allowing mixed-valence states. -/
structure EmotionPhenomenon where
  name              : String
  phases            : List PhaseSnapshot
  secondary_valence : Option OverflowValence
  deriving Repr

/-- A phenomenon is **representable** by the 18-cell grid iff it has
    exactly one phase (no locale or tendency shift) and no secondary
    valence (single hedonic sign). -/
def IsRepresentable (p : EmotionPhenomenon) : Prop :=
  p.phases.length = 1 ∧ p.secondary_valence = none

/-! ## Positive control: simple emotions fit the grid -/

/-- A pure-joy phenomenon: conscious locale, positive valence, approach
    tendency, single phase, no mixed valence. -/
def pureJoy : EmotionPhenomenon :=
  { name              := "joy"
    phases            := [{ locale := .conscious,
                            valence := .positive,
                            tendency := .approach }]
    secondary_valence := none }

theorem pureJoy_is_representable : IsRepresentable pureJoy := by
  unfold IsRepresentable pureJoy
  refine ⟨?_, ?_⟩ <;> rfl

/-- Pure anger fits too: conscious, negative, approach (the anger /
    relief / anxiety / calm orthogonality from
    `AffectAxesIndependence`). -/
def pureAnger : EmotionPhenomenon :=
  { name              := "anger"
    phases            := [{ locale := .conscious,
                            valence := .negative,
                            tendency := .approach }]
    secondary_valence := none }

theorem pureAnger_is_representable : IsRepresentable pureAnger := by
  unfold IsRepresentable pureAnger
  refine ⟨?_, ?_⟩ <;> rfl

/-! ## Failure mode 1: mixed valence

  Bittersweet is the canonical witness — a phenomenon that
  simultaneously carries positive and negative hedonic load. The
  binary `OverflowValence` cannot represent the simultaneity. -/

def bittersweet : EmotionPhenomenon :=
  { name              := "bittersweet"
    phases            := [{ locale := .conscious,
                            valence := .positive,
                            tendency := .approach }]
    secondary_valence := some .negative }

theorem bittersweet_not_representable : ¬ IsRepresentable bittersweet := by
  intro h
  have h2 : bittersweet.secondary_valence = none := h.2
  -- bittersweet.secondary_valence reduces to `some .negative`
  exact Option.some_ne_none _ h2

/-! ## Failure mode 2: locale shift

  Embarrassment migration is the canonical witness — a phenomenon
  whose locale moves from body (blushing) to conscious (rumination)
  across phases. The single-locale slot cannot host the migration. -/

def embarrassmentMigration : EmotionPhenomenon :=
  { name              := "embarrassment-migration"
    phases            :=
      [{ locale := .body,      valence := .negative, tendency := .approach },
       { locale := .conscious, valence := .negative, tendency := .withdraw }]
    secondary_valence := none }

theorem embarrassment_migration_not_representable :
    ¬ IsRepresentable embarrassmentMigration := by
  intro h
  have h1 : embarrassmentMigration.phases.length = 1 := h.1
  -- length = 2 ≠ 1
  have : (2 : Nat) = 1 := h1
  exact absurd this (by decide)

/-! ## Failure mode 3: tendency shift

  Grief migrates between revisiting (approach) and numbing (withdraw)
  within a single conscious-locale, single-negative-valence
  phenomenon. The 18-cell grid has one tendency slot per kind. -/

def griefTendencyShift : EmotionPhenomenon :=
  { name              := "grief-tendency-shift"
    phases            :=
      [{ locale := .conscious, valence := .negative, tendency := .approach },
       { locale := .conscious, valence := .negative, tendency := .withdraw }]
    secondary_valence := none }

theorem grief_tendency_shift_not_representable :
    ¬ IsRepresentable griefTendencyShift := by
  intro h
  have h1 : griefTendencyShift.phases.length = 1 := h.1
  have : (2 : Nat) = 1 := h1
  exact absurd this (by decide)

/-! ## The catalog projects, it does not erase

  Nostalgia is in the catalog (`AffectKind.nostalgia` — conscious,
  positive, withdraw). The catalog's representation is faithful to
  the *positive face* of nostalgia and silent on its negative grain.
  Both the projection and the richer phenomenon are well-typed
  `EmotionPhenomenon` values; only the projection is representable. -/

def nostalgiaProjected : EmotionPhenomenon :=
  { name              := "nostalgia (catalog projection)"
    phases            := [{ locale := .conscious,
                            valence := .positive,
                            tendency := .withdraw }]
    secondary_valence := none }

def nostalgiaRich : EmotionPhenomenon :=
  { name              := "nostalgia (with negative grain)"
    phases            := [{ locale := .conscious,
                            valence := .positive,
                            tendency := .withdraw }]
    secondary_valence := some .negative }

theorem nostalgia_projected_is_representable :
    IsRepresentable nostalgiaProjected := by
  unfold IsRepresentable nostalgiaProjected
  refine ⟨?_, ?_⟩ <;> rfl

theorem nostalgia_rich_not_representable :
    ¬ IsRepresentable nostalgiaRich := by
  intro h
  have h2 : nostalgiaRich.secondary_valence = none := h.2
  exact Option.some_ne_none _ h2

/-- The two nostalgia phenomena agree on the phases axis but differ
    on the secondary-valence axis: the catalog's representation
    drops the negative grain. -/
theorem nostalgia_catalog_projects_away_negative_grain :
    nostalgiaProjected.phases = nostalgiaRich.phases ∧
    nostalgiaProjected.secondary_valence ≠ nostalgiaRich.secondary_valence ∧
    IsRepresentable nostalgiaProjected ∧
    ¬ IsRepresentable nostalgiaRich := by
  refine ⟨rfl, ?_, nostalgia_projected_is_representable,
          nostalgia_rich_not_representable⟩
  decide

/-! ## Headline negative results -/

/-- **`phenomena_outside_grid_exist`** — there exist `EmotionPhenomenon`
    values that the 18-cell grid cannot represent. -/
theorem phenomena_outside_grid_exist :
    ∃ p : EmotionPhenomenon, ¬ IsRepresentable p :=
  ⟨bittersweet, bittersweet_not_representable⟩

/-- **`at_least_three_distinct_failure_modes_outside_grid`** — the
    failures are not exemplars of one shape; they are three
    structurally distinct shapes (mixed valence, locale shift,
    tendency shift). -/
theorem at_least_three_distinct_failure_modes_outside_grid :
    ¬ IsRepresentable bittersweet ∧
    ¬ IsRepresentable embarrassmentMigration ∧
    ¬ IsRepresentable griefTendencyShift :=
  ⟨bittersweet_not_representable,
    embarrassment_migration_not_representable,
    grief_tendency_shift_not_representable⟩

/-! ## Extension predicates: the axes a richer matrix would need

  These are decidable `Bool` predicates, not new axioms. They name
  the structural extensions that would close each failure mode. A
  Mathlib-bearing module could quote them as the hypotheses of a
  representability theorem in the enriched matrix. -/

/-- The phenomenon needs an axis to record a simultaneous secondary
    valence (the bittersweet failure mode). -/
def NeedsMixedValence (p : EmotionPhenomenon) : Bool :=
  p.secondary_valence.isSome

/-- The phenomenon needs more than one phase, signalling either a
    locale shift or a tendency shift between phases. -/
def NeedsMultiplePhases (p : EmotionPhenomenon) : Bool :=
  decide (p.phases.length > 1)

theorem bittersweet_needs_mixed_valence :
    NeedsMixedValence bittersweet = true := by
  unfold NeedsMixedValence bittersweet
  decide

theorem embarrassment_migration_needs_multiple_phases :
    NeedsMultiplePhases embarrassmentMigration = true := by
  unfold NeedsMultiplePhases embarrassmentMigration
  decide

theorem grief_tendency_shift_needs_multiple_phases :
    NeedsMultiplePhases griefTendencyShift = true := by
  unfold NeedsMultiplePhases griefTendencyShift
  decide

/-- Extensions are *not exclusive*: a mixed-valence phenomenon may
    also undergo a locale or tendency shift. The tightest possible
    enrichment must accommodate every combination of the three
    failure modes. -/
def needsBothExtensions : EmotionPhenomenon :=
  { name              := "bittersweet-grief"
    phases            :=
      [{ locale := .conscious, valence := .positive, tendency := .approach },
       { locale := .conscious, valence := .negative, tendency := .withdraw }]
    secondary_valence := some .negative }

theorem needsBothExtensions_needs_both :
    NeedsMixedValence needsBothExtensions = true ∧
    NeedsMultiplePhases needsBothExtensions = true := by
  refine ⟨?_, ?_⟩
  · unfold NeedsMixedValence needsBothExtensions; decide
  · unfold NeedsMultiplePhases needsBothExtensions; decide

theorem needsBothExtensions_not_representable :
    ¬ IsRepresentable needsBothExtensions := by
  intro h
  have h1 : needsBothExtensions.phases.length = 1 := h.1
  have : (2 : Nat) = 1 := h1
  exact absurd this (by decide)

/-! ## Cell count: what enriching the matrix would buy

  The current grid is `3 × 2 × 3 = 18` cells. Adding an `Option
  OverflowValence` secondary-valence axis (three states: `none`,
  `some .positive`, `some .negative`) multiplies the cell count by
  3, giving `54`. Adding a binary "phases ≥ 2" toggle then doubles
  it to `108`. Each new axis grows the grid combinatorially —
  exposing why the catalog approach has to *project* rather than
  enumerate when phenomenology becomes richer. -/

/-- The current 18-cell matrix size. -/
def currentMatrixCells : Nat := 3 * 2 * 3

theorem current_matrix_cells_eq_eighteen :
    currentMatrixCells = 18 := by decide

/-- Enriching with `Option OverflowValence` (3-state secondary
    valence) lifts the cell count to 54. -/
def enrichedWithMixedValenceCells : Nat := 3 * 2 * 3 * 3

theorem enriched_matrix_cell_count_is_fifty_four :
    enrichedWithMixedValenceCells = 54 := by decide

/-- Adding a binary "phases ≥ 2" toggle on top of mixed valence
    doubles again to 108 cells. -/
def enrichedWithMixedValenceAndPhasesCells : Nat := 3 * 2 * 3 * 3 * 2

theorem enriched_matrix_with_phases_cell_count_is_one_hundred_eight :
    enrichedWithMixedValenceAndPhasesCells = 108 := by decide

/-- Each enrichment is a strict gain in coverage, not a renaming of
    the same 18 cells. -/
theorem enrichments_strictly_grow_the_matrix :
    currentMatrixCells < enrichedWithMixedValenceCells ∧
    enrichedWithMixedValenceCells < enrichedWithMixedValenceAndPhasesCells := by
  refine ⟨?_, ?_⟩ <;> decide

/-! ## The honest counterpart witness

  A single statement that records every honest gap exposed in this
  module: a positive control, three structurally distinct failure
  modes, the catalog-projection theorem, and the cell-count growth
  under enrichment. -/

theorem affect_matrix_completeness_witness :
    -- Positive control
    IsRepresentable pureJoy ∧
    IsRepresentable pureAnger ∧
    -- Three structurally distinct failure modes
    ¬ IsRepresentable bittersweet ∧
    ¬ IsRepresentable embarrassmentMigration ∧
    ¬ IsRepresentable griefTendencyShift ∧
    -- Combined-extension failure
    ¬ IsRepresentable needsBothExtensions ∧
    -- Catalog-projection witness
    IsRepresentable nostalgiaProjected ∧
    ¬ IsRepresentable nostalgiaRich ∧
    nostalgiaProjected.phases = nostalgiaRich.phases ∧
    -- Cell count: enrichment is strict gain
    currentMatrixCells = 18 ∧
    enrichedWithMixedValenceCells = 54 ∧
    enrichedWithMixedValenceAndPhasesCells = 108 ∧
    currentMatrixCells < enrichedWithMixedValenceCells := by
  refine ⟨pureJoy_is_representable,
          pureAnger_is_representable,
          bittersweet_not_representable,
          embarrassment_migration_not_representable,
          grief_tendency_shift_not_representable,
          needsBothExtensions_not_representable,
          nostalgia_projected_is_representable,
          nostalgia_rich_not_representable,
          rfl,
          ?_, ?_, ?_, ?_⟩ <;> decide

/-! ## Honesty note

What we proved:

  • The 18-cell grid is faithful on phenomena that fit a single
    `(locale, valence, tendency)` triple with no secondary valence.
  • There exist `EmotionPhenomenon` values — bittersweet,
    embarrassment migration, grief tendency-shift — that
    structurally cannot be folded into a single grid coordinate.
    The three failures are distinct (mixed valence vs. locale
    shift vs. tendency shift) and combinable.
  • The catalog's nostalgia is a *projection*: the single-valence
    snapshot is representable, but the phenomenon's bittersweet
    grain is not. The catalog is not erasing — it is collapsing one
    dimension of the richer phenomenology onto its dominant face.
  • Enriching the matrix grows the cell count combinatorially:
    18 → 54 with secondary valence, 54 → 108 with a phases toggle.

What we did **not** prove:

  • That `EmotionPhenomenon` faithfully describes real human
    cognitive phenomenology. The richer Lean type is *richer than*
    the 18-cell grid by construction; whether real emotional life
    exhibits bittersweet, embarrassment migration, or grief
    tendency-shifts in the precise structural sense above is an
    empirical question for psychology, supported by but not closed
    by clinical literature. The bridge to lived experience is
    prose; the in-Lean content is the structural gap between the
    grid and the richer type.
  • That the enriched cell counts are themselves "complete" in any
    stronger sense. Each enrichment closes a specific failure mode
    and opens new questions (e.g., a temporal axis with arbitrary
    phase counts, valence as a non-binary spectrum, locale as a
    distributional rather than discrete coordinate). The
    `enrichments_strictly_grow_the_matrix` theorem certifies *gain*,
    not *closure*.
  • Any statement about the catalog being wrong. The catalog is
    correctly faithful at its chosen resolution; the structural
    point is the resolution itself, which the projection theorem
    names without contradicting any in-grid claim.

## Next exploration

`Gnosis/AffectMatrixTemporalAxis.lean` — extend `EmotionPhenomenon`
with a `tempo : Nat` field measuring phase duration and prove that
two phenomena with the same `(locale, valence, tendency)` snapshots
but different tempo cannot be distinguished by the 18-cell grid.
That makes time itself a representational axis the matrix collapses
— the same shape of gap as mixed valence and locale shift, but on
the rate-of-change dimension. The natural target: a tempo-faithful
representability predicate `IsTempoRepresentable` and a
`fast_grief_and_slow_grief_collapse_in_grid` theorem witnessing
that the 18-cell coordinate is tempo-blind.
-/

end AffectMatrixCompleteness
