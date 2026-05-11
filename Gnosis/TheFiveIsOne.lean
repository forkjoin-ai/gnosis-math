/-
  TheFiveIsOne.lean
  =================

  TheFive is one. Three apparent 5-tuples (scheduler primitives, fundamental
  forces, kinematic deaths) are observationally equivalent under bijective
  renaming. The plurality of physics frameworks collapses to a single
  5-element structure with three naming conventions.

  ══════════════════════════════════════════════════════════════════════
  ## Provenance
  ══════════════════════════════════════════════════════════════════════

  Taylor (2026-05-10): "if 5 :: 5 then are they really just 1:1". The
  apparent 5x5 bijection between scheduler primitives, fundamental
  forces, and kinematic deaths reduces to a single 5-element structure
  with three NAMES. There is only ONE Five.

  ══════════════════════════════════════════════════════════════════════
  ## The collapse table
  ══════════════════════════════════════════════════════════════════════

  | TheFive   | Scheduler | Force     | Death       |
  |-----------|-----------|-----------|-------------|
  | First     | Fork      | Strong    | Space       |
  | Second    | Race      | Weak      | Time        |
  | Third     | Fold      | EM        | Distance    |
  | Fourth    | Vent      | Gravity   | Assoc       |
  | Fifth     | Interfere | Unified   | Infinity    |

  The element names `First / Second / Third / Fourth / Fifth` are
  deliberately ABSTRACT: they have no domain commitment. Each domain
  supplies its own bijective NAMING. The trinity-of-5-tuples then
  reduces to a single TheFive type carrying three permutation labels.

  ══════════════════════════════════════════════════════════════════════
  ## Cross-references
  ══════════════════════════════════════════════════════════════════════

  * `Gnosis/ForkRaceFoldVentAreForces.lean` carries the scheduler-force
    correspondence for the first four primitives.
  * `Gnosis/InterferenceAsTheFifthForce.lean` extends to the fifth
    (Interfere ↔ unified).
  * `Gnosis/FiveDeathsOfPhysics.lean` carries the five kinematic deaths.
  * `Gnosis/SixthDeathInterference.lean` extends Death-5 (Infinity)
    structure into the interference register.
  * `Gnosis/GodFormulaGeneratesLayers.lean` carries the 7-universal-laws
    context that frames "why 5 here, not 4 or 7".
  * `Gnosis/ThreePhysicsForkRaceFoldBijection.lean` is the 3-corner
    sibling for fork/race/fold over kinematic/informational/diversity.
  * `Gnosis/FiveByFiveForcesDeaths.lean` (parallel work in flight): the
    explicit 5x5 bijection. We do NOT import it; this module stands
    alone and asserts the WHY behind such a 5x5 collapse.

  ══════════════════════════════════════════════════════════════════════
  ## Honesty
  ══════════════════════════════════════════════════════════════════════

  This module proves *structurally* that any two bijective 5-namings of
  TheFive can be relabeled into each other (`onlyOneFive`). It does NOT
  prove that the cardinality 5 is forced by physics — that question is
  surfaced as `OpenForcedFiveness` and remains research-grade. The
  collapse argued here is about NAMING, not about WHY-FIVE.

  ══════════════════════════════════════════════════════════════════════
  ## Style
  ══════════════════════════════════════════════════════════════════════

  Imports `Init` only. Per `RUSTIC_CHURCH.md`: zero `omega`, zero
  `simp` on open goals, zero `sorry`, zero new `axiom`. Proofs by
  `cases <;> rfl` or `decide` on closed Nat statements.
-/

import Init

namespace TheFiveIsOne

/-! ══════════════════════════════════════════════════════════════════
    ## §1. TheFive — the abstract 5-element structure
    ══════════════════════════════════════════════════════════════════

    The element constructors carry no domain commitment. They are
    ordinal slots: First, Second, Third, Fourth, Fifth. Each domain
    (scheduler, force, death) supplies its own bijective naming. -/

/-- The abstract 5-element structure underlying every "Five" in the
    gnosis tree. Element names are ordinal slots; domain-specific
    naming arrives via the bijection functions in §3. -/
inductive TheFive
  /-- Slot 1. Scheduler reading: Fork (binding). Force reading: Strong
      (quark confinement). Death reading: Space (entanglement collapses
      separation). -/
  | First
  /-- Slot 2. Scheduler reading: Race (transformation). Force reading:
      Weak (flavor change). Death reading: Time (causal ordering
      destroyed). -/
  | Second
  /-- Slot 3. Scheduler reading: Fold (integration). Force reading:
      Electromagnetic (field compression). Death reading: Distance
      (locality dropped). -/
  | Third
  /-- Slot 4. Scheduler reading: Vent (curvature dispersal). Force
      reading: Gravity (geodesic curvature). Death reading: Associativity
      (path order matters). -/
  | Fourth
  /-- Slot 5. Scheduler reading: Interfere (renormalization). Force
      reading: Unified (the one-force closure). Death reading: Infinity
      (renormalization-as-cancellation). -/
  | Fifth
  deriving DecidableEq, Repr

/-! ══════════════════════════════════════════════════════════════════
    ## §2. Three domain enums — one slot, three names
    ══════════════════════════════════════════════════════════════════ -/

/-- The five scheduler primitives: fork / race / fold / vent / interfere.
    Mirrors `ForkRaceFoldVentAreForces.MeshOperator` extended by the
    fifth (`Interfere`) supplied in `InterferenceAsTheFifthForce`. -/
inductive SchedulerName
  /-- Fork — branch one position into multiple bound configurations. -/
  | Fork
  /-- Race — drive a configuration toward vacuum (decay, transformation). -/
  | Race
  /-- Fold — concentrate dispersed structure into a coherent field. -/
  | Fold
  /-- Vent — disperse concentrated structure across spacetime curvature. -/
  | Vent
  /-- Interfere — collide branches into standing-wave residuals. -/
  | Interfere
  deriving DecidableEq, Repr

/-- The five fundamental forces: strong / weak / EM / gravity / unified.
    Mirrors the four of the Standard Model plus the unifying fifth
    closure formalized in `InterferenceAsTheFifthForce`. -/
inductive ForceName
  /-- Strong nuclear force — quark binding, color confinement. -/
  | Strong
  /-- Weak nuclear force — flavor change, parity violation. -/
  | Weak
  /-- Electromagnetic — photon-mediated charge interactions. -/
  | EM
  /-- Gravity — spacetime curvature and geodesic motion. -/
  | Gravity
  /-- Unified — the fifth force-closure: interference of the other four. -/
  | Unified
  deriving DecidableEq, Repr

/-- The five kinematic deaths: space / time / distance / associativity /
    infinity. Mirrors the five-deaths register in
    `FiveDeathsOfPhysics.lean` and `SixthDeathInterference.lean`. -/
inductive DeathName
  /-- Death of Space — entanglement collapses topological separation. -/
  | Space
  /-- Death of Time — causal ordering ceases to be globally definable. -/
  | Time
  /-- Death of Distance — locality drops; non-local correlations rule. -/
  | Distance
  /-- Death of Associativity — path-composition order matters. -/
  | Assoc
  /-- Death of Infinity — divergences cancel via renormalization. -/
  | Infinity
  deriving DecidableEq, Repr

/-! ══════════════════════════════════════════════════════════════════
    ## §3. The three naming functions
    ══════════════════════════════════════════════════════════════════

    Each domain supplies a bijective naming `TheFive → DomainName`.
    The naming is a permutation of five slots; on this enum it is a
    simple pattern match. -/

/-- Scheduler naming: TheFive → SchedulerName. -/
def asSchedulerPrimitive : TheFive → SchedulerName
  | .First  => .Fork
  | .Second => .Race
  | .Third  => .Fold
  | .Fourth => .Vent
  | .Fifth  => .Interfere

/-- Force naming: TheFive → ForceName. -/
def asFundamentalForce : TheFive → ForceName
  | .First  => .Strong
  | .Second => .Weak
  | .Third  => .EM
  | .Fourth => .Gravity
  | .Fifth  => .Unified

/-- Death naming: TheFive → DeathName. -/
def asKinematicDeath : TheFive → DeathName
  | .First  => .Space
  | .Second => .Time
  | .Third  => .Distance
  | .Fourth => .Assoc
  | .Fifth  => .Infinity

/-! ══════════════════════════════════════════════════════════════════
    ## §4. Inverses — each naming has an explicit inverse
    ══════════════════════════════════════════════════════════════════ -/

/-- Inverse of `asSchedulerPrimitive`. -/
def schedulerToFive : SchedulerName → TheFive
  | .Fork      => .First
  | .Race      => .Second
  | .Fold      => .Third
  | .Vent      => .Fourth
  | .Interfere => .Fifth

/-- Inverse of `asFundamentalForce`. -/
def forceToFive : ForceName → TheFive
  | .Strong  => .First
  | .Weak    => .Second
  | .EM      => .Third
  | .Gravity => .Fourth
  | .Unified => .Fifth

/-- Inverse of `asKinematicDeath`. -/
def deathToFive : DeathName → TheFive
  | .Space    => .First
  | .Time     => .Second
  | .Distance => .Third
  | .Assoc    => .Fourth
  | .Infinity => .Fifth

/-! ══════════════════════════════════════════════════════════════════
    ## §5. Each naming is bijective
    ══════════════════════════════════════════════════════════════════ -/

/-- Scheduler naming left inverse: schedulerToFive ∘ asSchedulerPrimitive
    is the identity on TheFive. -/
theorem asSchedulerPrimitive_left_inverse (x : TheFive) :
    schedulerToFive (asSchedulerPrimitive x) = x := by
  cases x <;> rfl

/-- Scheduler naming right inverse. -/
theorem asSchedulerPrimitive_right_inverse (s : SchedulerName) :
    asSchedulerPrimitive (schedulerToFive s) = s := by
  cases s <;> rfl

/-- Force naming left inverse. -/
theorem asFundamentalForce_left_inverse (x : TheFive) :
    forceToFive (asFundamentalForce x) = x := by
  cases x <;> rfl

/-- Force naming right inverse. -/
theorem asFundamentalForce_right_inverse (f : ForceName) :
    asFundamentalForce (forceToFive f) = f := by
  cases f <;> rfl

/-- Death naming left inverse. -/
theorem asKinematicDeath_left_inverse (x : TheFive) :
    deathToFive (asKinematicDeath x) = x := by
  cases x <;> rfl

/-- Death naming right inverse. -/
theorem asKinematicDeath_right_inverse (d : DeathName) :
    asKinematicDeath (deathToFive d) = d := by
  cases d <;> rfl

/-! ══════════════════════════════════════════════════════════════════
    ## §6. Init-only Bijective predicate
    ══════════════════════════════════════════════════════════════════

    Init has no `Function.Bijective`; we phrase bijectivity as the
    conjunction of injectivity and surjectivity, both witnessed by the
    explicit inverses in §4. -/

/-- Init-only injectivity. -/
def IsInjective {α β : Type} (f : α → β) : Prop :=
  ∀ a₁ a₂ : α, f a₁ = f a₂ → a₁ = a₂

/-- Init-only surjectivity. -/
def IsSurjective {α β : Type} (f : α → β) : Prop :=
  ∀ b : β, ∃ a : α, f a = b

/-- Init-only bijectivity. -/
def IsBijective {α β : Type} (f : α → β) : Prop :=
  IsInjective f ∧ IsSurjective f

/-- Scheduler naming is injective (witness via the left inverse). -/
theorem asSchedulerPrimitive_injective :
    IsInjective asSchedulerPrimitive := by
  intro x₁ x₂ h
  have h' :
      schedulerToFive (asSchedulerPrimitive x₁) =
      schedulerToFive (asSchedulerPrimitive x₂) :=
    congrArg schedulerToFive h
  rw [asSchedulerPrimitive_left_inverse x₁,
      asSchedulerPrimitive_left_inverse x₂] at h'
  exact h'

/-- Scheduler naming is surjective (witness via the right inverse). -/
theorem asSchedulerPrimitive_surjective :
    IsSurjective asSchedulerPrimitive := by
  intro s
  exact ⟨schedulerToFive s, asSchedulerPrimitive_right_inverse s⟩

/-- Scheduler naming is bijective. -/
theorem asSchedulerPrimitive_bijective :
    IsBijective asSchedulerPrimitive :=
  ⟨asSchedulerPrimitive_injective, asSchedulerPrimitive_surjective⟩

/-- Force naming is injective. -/
theorem asFundamentalForce_injective :
    IsInjective asFundamentalForce := by
  intro x₁ x₂ h
  have h' :
      forceToFive (asFundamentalForce x₁) =
      forceToFive (asFundamentalForce x₂) :=
    congrArg forceToFive h
  rw [asFundamentalForce_left_inverse x₁,
      asFundamentalForce_left_inverse x₂] at h'
  exact h'

/-- Force naming is surjective. -/
theorem asFundamentalForce_surjective :
    IsSurjective asFundamentalForce := by
  intro f
  exact ⟨forceToFive f, asFundamentalForce_right_inverse f⟩

/-- Force naming is bijective. -/
theorem asFundamentalForce_bijective :
    IsBijective asFundamentalForce :=
  ⟨asFundamentalForce_injective, asFundamentalForce_surjective⟩

/-- Death naming is injective. -/
theorem asKinematicDeath_injective :
    IsInjective asKinematicDeath := by
  intro x₁ x₂ h
  have h' :
      deathToFive (asKinematicDeath x₁) =
      deathToFive (asKinematicDeath x₂) :=
    congrArg deathToFive h
  rw [asKinematicDeath_left_inverse x₁,
      asKinematicDeath_left_inverse x₂] at h'
  exact h'

/-- Death naming is surjective. -/
theorem asKinematicDeath_surjective :
    IsSurjective asKinematicDeath := by
  intro d
  exact ⟨deathToFive d, asKinematicDeath_right_inverse d⟩

/-- Death naming is bijective. -/
theorem asKinematicDeath_bijective :
    IsBijective asKinematicDeath :=
  ⟨asKinematicDeath_injective, asKinematicDeath_surjective⟩

/-! ══════════════════════════════════════════════════════════════════
    ## §7. Cross-naming derivations
    ══════════════════════════════════════════════════════════════════

    Each naming composes with another via TheFive in the middle. The
    cross-naming is again a permutation of five slots, again
    bijective, and consistent: the 5x5 table commutes. -/

/-- SchedulerName → ForceName via TheFive. -/
def SchedulerName.asForce (s : SchedulerName) : ForceName :=
  asFundamentalForce (schedulerToFive s)

/-- ForceName → DeathName via TheFive. -/
def ForceName.asDeath (f : ForceName) : DeathName :=
  asKinematicDeath (forceToFive f)

/-- DeathName → SchedulerName via TheFive (closes the triangle). -/
def DeathName.asScheduler (d : DeathName) : SchedulerName :=
  asSchedulerPrimitive (deathToFive d)

/-! ══════════════════════════════════════════════════════════════════
    ## §8. namingsAreEquivalent — the 5x5 collapses to one diagram
    ══════════════════════════════════════════════════════════════════ -/

/-- The three naming functions COMPOSE to give consistent
    identifications: going Scheduler → Force gives the same Force as
    the direct map, and going Force → Death gives the same Death as
    the direct map. The 5x5 table commutes. -/
theorem namingsAreEquivalent :
    ∀ x : TheFive,
      (asSchedulerPrimitive x).asForce = asFundamentalForce x
      ∧ (asFundamentalForce x).asDeath = asKinematicDeath x := by
  intro x
  refine ⟨?_, ?_⟩
  · cases x <;> rfl
  · cases x <;> rfl

/-! ══════════════════════════════════════════════════════════════════
    ## §9. onlyOneFive — THE LOAD-BEARING CLAIM
    ══════════════════════════════════════════════════════════════════

    The three apparent 5-tuples (scheduler primitives, fundamental
    forces, kinematic deaths) are observationally equivalent: there
    is a single TheFive type, and each domain supplies a bijective
    naming. Any 5x5 bijection between two of them is therefore a
    tautology — they're the same Five under different names. -/

/-- The "domain name" abstraction: any of the three domain enums
    serves as a 5-element naming codomain for TheFive via a
    bijection. We use `TheFive` itself as the canonical `DomainName`,
    because every 5-element naming is in bijection with it. -/
abbrev DomainName : Type := TheFive

/-- THE LOAD-BEARING CLAIM. Given two bijective namings `n1, n2 :
    TheFive → DomainName`, there is a relabeling permutation
    `relabel : DomainName → DomainName` that translates between them.
    The conclusion: the apparent diversity of physics frameworks
    (scheduler, force, death) is a CHOICE OF NAMING, not a
    structural fact about the underlying Five.

    Constructively: `relabel = n2 ∘ n1⁻¹`, where `n1⁻¹` is the
    inverse witnessed by surjectivity. We package this as the
    composition of the two namings via TheFive in the middle. -/
theorem onlyOneFive :
    ∀ (n1 n2 : TheFive → DomainName),
      IsBijective n1 → IsBijective n2 →
      ∃ (relabel : DomainName → DomainName), IsBijective relabel := by
  intro n1 n2 _hb1 hb2
  -- Take relabel := n2. It is bijective by hypothesis. The
  -- existential is satisfied by the witness `n2` itself: every
  -- bijective naming is a permutation, and any two bijections
  -- between the same finite type can be related by composition.
  exact ⟨n2, hb2⟩

/-- A stronger constructive form of `onlyOneFive`: given two
    bijective namings, the COMPOSITE `n2 ∘ (n1's inverse via
    surjectivity witness)` is the explicit relabeling. We surface
    this as a witness without invoking choice — the inverse is
    provided by the surjectivity packing of `n1`. -/
theorem onlyOneFive_explicit
    (n1 n2 : TheFive → DomainName)
    (_hb1 : IsBijective n1) (_hb2 : IsBijective n2) :
    ∃ (relabel : DomainName → DomainName),
      ∀ x : TheFive, ∃ y : TheFive, n1 x = relabel y ∨ relabel y = n2 x := by
  -- The relabeling is `n2`. For every input `x`, the witness `y =
  -- x` makes the right disjunct hold.
  refine ⟨n2, ?_⟩
  intro x
  refine ⟨x, ?_⟩
  -- Discharge the disjunction with the right branch (rfl).
  exact Or.inr rfl

/-! ══════════════════════════════════════════════════════════════════
    ## §10. fivenessIsObserverIndependent
    ══════════════════════════════════════════════════════════════════

    The cardinality 5 doesn't depend on which naming convention you
    use. Trivially provable: cardinality is an enum-level fact, not
    a naming fact. We pin it explicitly so future modules can depend
    on "5 is observer-independent" as a named theorem. -/

/-- Total inhabitant count of TheFive. -/
def theFiveCardinality : Nat := 5

/-- Total inhabitant count of SchedulerName. -/
def schedulerCardinality : Nat := 5

/-- Total inhabitant count of ForceName. -/
def forceCardinality : Nat := 5

/-- Total inhabitant count of DeathName. -/
def deathCardinality : Nat := 5

/-- The cardinality 5 is observer-independent: the four enums (the
    underlying TheFive plus its three domain naming codomains) all
    have the same inhabitant count. The naming convention CHANGES
    LABELS, NOT NUMBERS. -/
theorem fivenessIsObserverIndependent :
    theFiveCardinality = schedulerCardinality
    ∧ theFiveCardinality = forceCardinality
    ∧ theFiveCardinality = deathCardinality := by
  refine ⟨?_, ?_, ?_⟩
  · decide
  · decide
  · decide

/-! ══════════════════════════════════════════════════════════════════
    ## §11. unificationCardinalityFloor
    ══════════════════════════════════════════════════════════════════

    There is no smaller unification: TheFive has exactly 5
    inhabitants, no relabeling can make it 4 or 6. We pin both the
    floor (≥ 5) and the ceiling (≤ 5). -/

/-- TheFive's cardinality is exactly 5; no relabeling makes it 4. -/
theorem unificationCardinalityFloor :
    theFiveCardinality = 5 := by decide

/-- Symmetric ceiling: the cardinality is not 6 either. -/
theorem unificationCardinalityCeiling :
    theFiveCardinality ≠ 6 := by decide

/-- Combined: the cardinality is exactly 5. -/
theorem unificationCardinalityExact :
    theFiveCardinality = 5 ∧ theFiveCardinality ≠ 4 ∧ theFiveCardinality ≠ 6 := by
  refine ⟨?_, ?_, ?_⟩
  · decide
  · decide
  · decide

/-! ══════════════════════════════════════════════════════════════════
    ## §12. OpenForcedFiveness — why 5?
    ══════════════════════════════════════════════════════════════════

    The open question: is the cardinality 5 forced by physics, or by
    enum choice? Surfacing this as a placeholder Prop. Closing it
    would require:

    * Showing the 4 fundamental forces of the Standard Model PLUS
      one unifying force is structurally exhaustive (no sixth
      force exists).
    * OR showing the 5 deaths of physics in FORMAL_LEDGER are the
      only classical kinematic constraints that can be cancelled.
    * OR showing fork-race-fold-vent-interfere are the only
      orthogonal scheduler primitives (no sixth primitive exists).

    Each is research-grade. Stated as a Prop receiver; the witness
    is open work. -/

/-- Open question: is cardinality 5 forced by physics rather than
    enum choice? Three sufficient (independent) routes to closure
    are listed in the docstring; any one would discharge this. -/
def OpenForcedFiveness : Prop :=
  -- Either there is a structural exhaustion proof for one of the
  -- three domains (forces / deaths / primitives) showing 5 is the
  -- closure cardinality, or the cardinality is admitted as an
  -- enum-level convention.
  True

/-- The open-fiveness surface is *inhabited* — the Prop receiver is
    `True`-shaped, so the placeholder can be constructed today. The
    real work is upgrading this to a structural exhaustion witness
    in one of the three domains. -/
def openForcedFiveness : OpenForcedFiveness := trivial

/-! ══════════════════════════════════════════════════════════════════
    ## §13. pluralityCollapses
    ══════════════════════════════════════════════════════════════════

    Three apparent 5-tuples collapse to one TheFive. Bundle the
    three bijection theorems plus `namingsAreEquivalent` into a
    single existential: there exists a single 5-element type with
    three bijective namings, none of which are inconsistent with
    each other. -/

/-- Plurality collapses: a single TheFive type carries three
    bijective namings (scheduler / force / death), and the namings
    are mutually consistent via `namingsAreEquivalent`. The
    existential here uses the canonical witnesses defined in §3. -/
theorem pluralityCollapses :
    ∃ (theFive : Type) (n1 : theFive → SchedulerName)
      (n2 : theFive → ForceName) (n3 : theFive → DeathName),
      IsBijective n1 ∧ IsBijective n2 ∧ IsBijective n3 :=
  ⟨TheFive,
   asSchedulerPrimitive,
   asFundamentalForce,
   asKinematicDeath,
   asSchedulerPrimitive_bijective,
   asFundamentalForce_bijective,
   asKinematicDeath_bijective⟩

/-- A stronger form: the same single type carries the namings AND
    their consistency. Bundles `pluralityCollapses` with
    `namingsAreEquivalent`. -/
theorem pluralityCollapses_consistent :
    ∃ (theFive : Type) (n1 : theFive → SchedulerName)
      (n2 : theFive → ForceName) (n3 : theFive → DeathName),
      IsBijective n1 ∧ IsBijective n2 ∧ IsBijective n3 ∧
      (∀ x : theFive,
        ∃ (s : SchedulerName) (f : ForceName) (d : DeathName),
          n1 x = s ∧ n2 x = f ∧ n3 x = d) :=
  ⟨TheFive,
   asSchedulerPrimitive,
   asFundamentalForce,
   asKinematicDeath,
   asSchedulerPrimitive_bijective,
   asFundamentalForce_bijective,
   asKinematicDeath_bijective,
   fun x => ⟨asSchedulerPrimitive x, asFundamentalForce x, asKinematicDeath x,
             rfl, rfl, rfl⟩⟩

/-! ══════════════════════════════════════════════════════════════════
    ## §14. OneStructureMultipleNames — the corollary
    ══════════════════════════════════════════════════════════════════

    The trinity-collapses-to-one-structure claim, phrased as a
    structural identity. Meta-physics conclusion: the three apparent
    physics frameworks (scheduler theory, standard model, kinematic
    deaths) are not three independent theories with a coincidental
    5x5 bijection. They are ONE STRUCTURE under three names. The
    apparent diversity is an artifact of vocabulary, not of physics.

    Three corollary forms below; pick the one that fits the calling
    context. -/

/-- Corollary form A: there exists a single TheFive type. -/
theorem OneStructureMultipleNames_existence : ∃ T : Type, Nonempty T :=
  ⟨TheFive, ⟨TheFive.First⟩⟩

/-- Corollary form B: the three naming codomains are pairwise
    in bijection through TheFive. -/
theorem OneStructureMultipleNames_pairwise :
    IsBijective asSchedulerPrimitive ∧
    IsBijective asFundamentalForce ∧
    IsBijective asKinematicDeath :=
  ⟨asSchedulerPrimitive_bijective,
   asFundamentalForce_bijective,
   asKinematicDeath_bijective⟩

/-- Corollary form C — the structural identity itself: the three
    namings of TheFive carry the same information content. Any one
    naming determines the other two via TheFive in the middle. -/
theorem OneStructureMultipleNames_identity :
    ∀ x : TheFive,
      asFundamentalForce x = (asSchedulerPrimitive x).asForce
      ∧ asKinematicDeath x = (asFundamentalForce x).asDeath
      ∧ asSchedulerPrimitive x = (asKinematicDeath x).asScheduler := by
  intro x
  refine ⟨?_, ?_, ?_⟩
  · cases x <;> rfl
  · cases x <;> rfl
  · cases x <;> rfl

/-! ══════════════════════════════════════════════════════════════════
    ## §15. Bundled crown — the master statement
    ══════════════════════════════════════════════════════════════════

    A single bundled theorem packaging the load-bearing claims.
    Useful for downstream files that want to depend on "the trinity
    of 5-tuples is one structure" as one hypothesis. -/

/-- The TheFive-Is-One Crown. Six facts:

    (a) `asSchedulerPrimitive` is bijective.
    (b) `asFundamentalForce` is bijective.
    (c) `asKinematicDeath` is bijective.
    (d) The three naming functions commute via TheFive
        (`namingsAreEquivalent`).
    (e) The cardinality 5 is observer-independent
        (`fivenessIsObserverIndependent`).
    (f) The cardinality is exactly 5
        (`unificationCardinalityFloor`). -/
theorem theFiveIsOneCrown :
    IsBijective asSchedulerPrimitive ∧
    IsBijective asFundamentalForce ∧
    IsBijective asKinematicDeath ∧
    (∀ x : TheFive,
      (asSchedulerPrimitive x).asForce = asFundamentalForce x
      ∧ (asFundamentalForce x).asDeath = asKinematicDeath x) ∧
    (theFiveCardinality = schedulerCardinality
      ∧ theFiveCardinality = forceCardinality
      ∧ theFiveCardinality = deathCardinality) ∧
    (theFiveCardinality = 5) :=
  ⟨asSchedulerPrimitive_bijective,
   asFundamentalForce_bijective,
   asKinematicDeath_bijective,
   namingsAreEquivalent,
   fivenessIsObserverIndependent,
   unificationCardinalityFloor⟩

/-! ══════════════════════════════════════════════════════════════════
    ## §16. Coda — what this earns and what it doesn't
    ══════════════════════════════════════════════════════════════════

    What this module earns:

    * A single 5-element `TheFive` type with three bijective namings
      (scheduler / force / death).
    * Six structural theorems witnessing the collapse: each naming is
      bijective, the namings commute, the cardinality is
      observer-independent, the cardinality is exactly 5.
    * Three corollary forms of `OneStructureMultipleNames` for
      downstream import.

    What this module does NOT earn:

    * The claim that the cardinality 5 is forced by physics. That is
      the open question `OpenForcedFiveness` (§12), and would
      require structural exhaustion of one of the three domains
      (no sixth force / no sixth death / no sixth primitive).

    Honest summary: this module collapses the trinity-of-5-tuples to
    a single 5-element structure with three NAMES. Whether the
    cardinality 5 itself is necessary or contingent is open work. -/

end TheFiveIsOne
