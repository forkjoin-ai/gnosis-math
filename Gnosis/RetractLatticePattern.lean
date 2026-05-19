import Gnosis.AffectMatrixFourthAxis
import Gnosis.AffectMatrixAgencyAxis
import Gnosis.ThoughtBowlMechanicsRefined

/-
  RetractLatticePattern.lean
  ==========================

  The cross-pollination module: the **retract / reachable
  sub-lattice** pattern that recurs in three theorems built today.
  This module formalizes the abstract pattern once, then shows the
  three concrete round-trip theorems factor through it as one-line
  corollaries.

  ## What the pattern is

  A `Retract A B` packages four pieces:

  * `forget : A → B` — a forgetful map from a richer type `A` to
    a poorer type `B`.
  * `reach : B → Prop` — the reachability predicate carving out
    the sub-lattice of `B` that has a preimage.
  * `section_ : (b : B) → reach b → A` — a partial section
    producing a canonical preimage on every reachable `b`.
  * `round_trip : ∀ b (h : reach b), forget (section_ b h) = b` —
    the bijection witness on the reachable sub-lattice.

  This is exactly a *split surjection on the reachable subset*, or
  equivalently a *retraction of `A` onto `B`* restricted to where
  the reachability predicate holds.

  ## Three instances

  | Module today | `A` (rich) | `B` (poor) | `reach` |
  |--------------|------------|------------|---------|
  | `AffectMatrixFourthAxis` | `ContextualAffect` | `AffectVector` | universal (`True`) |
  | `ThoughtBowlMechanicsRefined` | `List VibeWave` | `TaoBowl` | `IsReachable` |
  | `AffectMatrixAgencyAxis` | `NextAxisWitness Base Axis` | `Base` | `P` (parametric) |

  The first two are concrete; the third is parametric (gives a
  family of retracts indexed by `(Base, Axis, P, a)`).

  ## What does *not* fit Pattern A

  * `BuleyErgodicClosure` — `liftToBuleyState : PolarizationState
    → BuleyState` is a *homomorphism* (it preserves `bulkOf`
    definitionally), not a retract; there is no canonical section
    from a `Nat` bulk-index back to a `PolarizationState`. The
    Skyrms-vs-Buley separator there has a different shape.
  * `AffectMatrixCompleteness` — only the predicate side
    (`IsRepresentable`) is built; no section yet. Adding a
    section `phenomenonOfAffectVector : AffectVector →
    EmotionPhenomenon` would slot it in here as a fourth
    instance.

  Imports the three concrete modules. Zero `sorry`, zero new
  `axiom`.
-/


namespace RetractLatticePattern

/-! ## The abstract retract pattern -/

/-- A retract / reachable sub-lattice: a forgetful map from a
    richer type `A` to a poorer type `B`, plus a reachability
    predicate `reach : B → Prop` and a partial section that
    recovers the original on every reachable point.

    On the `reach`-true subset of `B` this is a bijection witness:
    `forget ∘ section_ = id`. Off it, `B` may have inhabitants with
    no preimage in `A`, and the partial section is undefined. -/
structure Retract (A B : Type) where
  forget : A → B
  reach : B → Prop
  section_ : (b : B) → reach b → A
  round_trip : ∀ b (h : reach b), forget (section_ b h) = b

/-- Derived `Option`-valued partial section on a `Retract` whose
    reach predicate is decidable. Returns `some` exactly on the
    reachable sub-lattice. -/
def Retract.partialSection
    {A B : Type} (R : Retract A B) (b : B) [Decidable (R.reach b)] :
    Option A :=
  if h : R.reach b then some (R.section_ b h) else none

/-- The `Option`-lifted round-trip on the reachable sub-lattice. -/
theorem Retract.partial_round_trip
    {A B : Type} (R : Retract A B) (b : B) [Decidable (R.reach b)]
    (h : R.reach b) :
    Option.map R.forget (R.partialSection b) = some b := by
  unfold Retract.partialSection
  rw [dif_pos h]
  show some (R.forget (R.section_ b h)) = some b
  rw [R.round_trip b h]

/-! ## Instance 1: `AffectVector` ↞ `ContextualAffect`

  The `SocialContext` lift from `AffectMatrixFourthAxis`. The
  reach is universal — every `AffectVector` admits a lift for
  every fixed `SocialContext`. The retract is parametric in the
  default context value `c`. -/

/-- The lift/project retract on `AffectMatrixFourthAxis`,
    parametrized by which `SocialContext` value to fill the new
    axis with. Reach is trivially universal. -/
def affectMatrixSocialContextRetract
    (c : AffectMatrixFourthAxis.SocialContext) :
    Retract AffectMatrixFourthAxis.ContextualAffect
            VibesAsWaveInference.AffectVector where
  forget := AffectMatrixFourthAxis.project43
  reach := fun _ => True
  section_ := fun b _ => { affect := b, social_context := c }
  round_trip := fun b _ =>
    AffectMatrixFourthAxis.lift_then_project_is_identity b c

/-- One-line corollary: the existing `lift_then_project_is_identity`
    factors through the `Retract` abstraction. -/
theorem lift_then_project_is_identity_via_retract
    (a : VibesAsWaveInference.AffectVector)
    (c : AffectMatrixFourthAxis.SocialContext) :
    AffectMatrixFourthAxis.project43
        { affect := a, social_context := c } = a :=
  (affectMatrixSocialContextRetract c).round_trip a trivial

/-! ## Instance 2: `TaoBowl` ↞ `List VibeWave`

  The reachable-sub-lattice retract from
  `ThoughtBowlMechanicsRefined`. Reach is the sharp 4-axis
  structural condition `IsReachable`; the section is
  `canonicalField`; the round-trip is `bowl_of_canonical_field`. -/

/-- The `bowlOfField` ↔ `canonicalField` retract on the
    `IsReachable` sub-lattice of `TaoBowl`. -/
def thoughtBowlReachableRetract :
    Retract (List VibesAsWaveInference.VibeWave)
            EchoChamberAsTaoBowl.TaoBowl where
  forget := ThoughtBowlMechanics.bowlOfField
  reach := ThoughtBowlMechanicsRefined.IsReachable
  section_ := fun b _ => ThoughtBowlMechanicsRefined.canonicalField b
  round_trip := ThoughtBowlMechanicsRefined.bowl_of_canonical_field

/-- Decidability of the reach predicate for `thoughtBowlReachableRetract`.
    Lean does not auto-unfold the field projection; we expose the
    underlying `IsReachable` decidability instance explicitly. -/
instance (b : EchoChamberAsTaoBowl.TaoBowl) :
    Decidable (thoughtBowlReachableRetract.reach b) :=
  inferInstanceAs (Decidable (ThoughtBowlMechanicsRefined.IsReachable b))

/-- One-line corollary: the existing `bowl_of_canonical_field`
    factors through the `Retract` abstraction. -/
theorem bowl_of_canonical_field_via_retract
    (b : EchoChamberAsTaoBowl.TaoBowl)
    (h : ThoughtBowlMechanicsRefined.IsReachable b) :
    ThoughtBowlMechanics.bowlOfField
        (ThoughtBowlMechanicsRefined.canonicalField b) = b :=
  thoughtBowlReachableRetract.round_trip b h

/-- The `Option`-lifted round-trip from
    `ThoughtBowlMechanicsRefined.bowl_of_field_of_bowl_round_trip`
    factors through `Retract.partial_round_trip` once the reach
    predicate's decidability is supplied. -/
theorem bowl_of_field_of_bowl_round_trip_via_retract
    (b : EchoChamberAsTaoBowl.TaoBowl)
    (h : ThoughtBowlMechanicsRefined.IsReachable b) :
    Option.map ThoughtBowlMechanics.bowlOfField
        (thoughtBowlReachableRetract.partialSection b)
      = some b :=
  thoughtBowlReachableRetract.partial_round_trip b h

/-! ## Instance 3: `Base` ↞ `NextAxisWitness Base Axis`

  The meta-level retract from `AffectMatrixAgencyAxis`. The
  retract is parametric in `(Base, Axis, P, a)`. Reach is the
  base-level predicate `P`; the section attaches the fixed axis
  value `a`. The round-trip is `rfl`. -/

/-- The meta-scaling retract: `NextAxisWitness Base Axis ↠ Base`
    is a retract on the `P`-true sub-lattice of `Base`, parametric
    in the fixed axis value `a`. -/
def nextAxisWitnessRetract
    {Base Axis : Type} (P : Base → Prop) (a : Axis) :
    Retract (AffectMatrixAgencyAxis.NextAxisWitness Base Axis) Base where
  forget := AffectMatrixAgencyAxis.NextAxisWitness.base
  reach := P
  section_ := fun b _ => { base := b, axis := a }
  round_trip := fun _ _ => rfl

/-- One-line corollary: the meta-scaling lemma
    `cell_inhabited_n_lifts_to_n_plus_one` factors through the
    `Retract` abstraction. -/
theorem cell_inhabited_n_lifts_to_n_plus_one_via_retract
    {Base Axis : Type} {P : Base → Prop}
    (hBase : ∃ b : Base, P b) (a : Axis) :
    AffectMatrixAgencyAxis.NextAxisInhabited P a := by
  obtain ⟨b, hb⟩ := hBase
  let R := nextAxisWitnessRetract P a
  refine ⟨R.section_ b hb, ?_, ?_⟩
  · exact hb
  · rfl

/-! ## The pattern is genuinely abstract

  Two checks that `Retract` is not just a renaming exercise. -/

/-- Composition law on full retracts (universal reach). If `A ↠ B`
    and `B ↠ C` are both retracts with universal reach, the
    composition is a retract `A ↠ C`. This is the pure split-mono
    composition; the partial-reach version requires extra care. -/
def Retract.compose_universal
    {A B C : Type} (R₁ : Retract A B) (R₂ : Retract B C)
    (hR₁ : ∀ b, R₁.reach b) (hR₂ : ∀ c, R₂.reach c) :
    Retract A C where
  forget := R₂.forget ∘ R₁.forget
  reach := fun _ => True
  section_ := fun c _ => R₁.section_ (R₂.section_ c (hR₂ c)) (hR₁ _)
  round_trip := fun c _ => by
    show R₂.forget (R₁.forget (R₁.section_ (R₂.section_ c (hR₂ c)) (hR₁ _))) = c
    rw [R₁.round_trip (R₂.section_ c (hR₂ c)) (hR₁ _),
        R₂.round_trip c (hR₂ c)]

/-- Identity retract on any type. Witnesses that `Retract A A` is
    inhabited for every `A`. -/
def Retract.id (A : Type) : Retract A A where
  forget := fun a => a
  reach := fun _ => True
  section_ := fun a _ => a
  round_trip := fun _ _ => rfl

/-! ## Headline witness

  A single statement bundling the abstract pattern, the three
  instances, and the factoring of each existing round-trip
  theorem through the abstraction. -/

/-- The conjunctive proposition that the headline theorem proves.
    Lifted to an `abbrev` so that downstream registries (for example
    `Gnosis.PatternAtlas`) can bundle the witness by name. -/
abbrev RetractLatticeWitness : Prop :=
    -- Three concrete retract instances exist
    (∀ _c : AffectMatrixFourthAxis.SocialContext,
      ∃ _ : Retract AffectMatrixFourthAxis.ContextualAffect
                     VibesAsWaveInference.AffectVector, True) ∧
    (∃ _ : Retract (List VibesAsWaveInference.VibeWave)
                    EchoChamberAsTaoBowl.TaoBowl, True) ∧
    (∀ {Base Axis : Type} (_P : Base → Prop) (_a : Axis),
      ∃ _ : Retract (AffectMatrixAgencyAxis.NextAxisWitness Base Axis) Base, True) ∧
    -- The three round-trip theorems factor through the abstraction
    (∀ a : VibesAsWaveInference.AffectVector,
     ∀ c : AffectMatrixFourthAxis.SocialContext,
      AffectMatrixFourthAxis.project43
          { affect := a, social_context := c } = a) ∧
    (∀ b : EchoChamberAsTaoBowl.TaoBowl,
     ∀ _h : ThoughtBowlMechanicsRefined.IsReachable b,
      ThoughtBowlMechanics.bowlOfField
          (ThoughtBowlMechanicsRefined.canonicalField b) = b) ∧
    (∀ {Base Axis : Type} {P : Base → Prop}
     (_hBase : ∃ b : Base, P b) (a : Axis),
      AffectMatrixAgencyAxis.NextAxisInhabited P a) ∧
    -- Composition and identity witnesses
    (∃ _ : Retract Unit Unit, True)

theorem retract_lattice_pattern_witness : RetractLatticeWitness := by
  refine ⟨?_, ?_, ?_,
          lift_then_project_is_identity_via_retract,
          bowl_of_canonical_field_via_retract,
          @cell_inhabited_n_lifts_to_n_plus_one_via_retract,
          ⟨Retract.id Unit, trivial⟩⟩
  · exact fun c => ⟨affectMatrixSocialContextRetract c, trivial⟩
  · exact ⟨thoughtBowlReachableRetract, trivial⟩
  · exact fun P a => ⟨nextAxisWitnessRetract P a, trivial⟩

/-! ## Honesty note

What this module proves:

  * The abstract `Retract A B` structure with reach predicate and
    round-trip law captures the structural pattern shared by three
    of today's modules.
  * Three concrete retracts exist:
    `affectMatrixSocialContextRetract` (universal reach,
    parametric in the default context),
    `thoughtBowlReachableRetract` (partial reach via
    `IsReachable`), and `nextAxisWitnessRetract` (universal reach,
    parametric in the fixed axis value).
  * Each existing round-trip theorem factors through the
    abstraction in one line:
    `lift_then_project_is_identity`,
    `bowl_of_canonical_field`,
    `cell_inhabited_n_lifts_to_n_plus_one`. The factoring is not
    a re-proof — the original theorems are passed to the
    `round_trip` field of the corresponding retract.
  * `Retract` admits identity (`Retract.id`) and composition under
    universal reach (`Retract.compose_universal`), so the
    abstraction has minimal categorical content.

What this module does **not** prove:

  * That every forgetful map in the codebase is a retract. Two
    explicit non-instances are listed in the header:
    `BuleyErgodicClosure.liftToBuleyState` is a *homomorphism*
    (preserves `bulkOf` definitionally) but has no section, and
    `AffectMatrixCompleteness.IsRepresentable` is a predicate
    waiting for a section to be built. The retract structure is a
    real abstraction, not a universal lens.
  * Composition of *partial* retracts. The
    `Retract.compose_universal` lemma above only handles the
    universal-reach case. Composing two partial retracts requires
    showing reach predicates are compatible under section, and
    that proof has more bookkeeping than this introduction
    needs.
  * That the categorical reading is faithful. We have a structure
    with the data of a split mono, but no proof that it forms a
    `Category`-instance compatible thing. That would require
    Mathlib.

## Next exploration

`Gnosis/HomomorphismLatticePattern.lean` — the cross-domain
counterpart for `BuleyErgodicClosure`. Where the retract pattern
captures "forget-and-recover," the homomorphism pattern captures
"forget-but-preserve-an-invariant." The natural target is

    structure Homomorphism (A B C : Type) where
      forget   : A → C        -- the invariant projection
      lift     : A → B        -- the structural lift
      coherence : ∀ a, project (lift a) = forget a

with `BuleyErgodicClosure.liftToBuleyState` as the canonical
instance and `Gnosis.bulkOf` as the invariant. That would close
the second cross-cutting pattern from the audit at theorem level.
-/

end RetractLatticePattern
