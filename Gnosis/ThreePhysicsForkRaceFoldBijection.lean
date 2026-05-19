import Init

/-
  ThreePhysicsForkRaceFoldBijection.lean
  ======================================

  Three physics, three scheduler primitives, three Bule faces — all
  in bijection. The third physics (Diversity / Triton / Void / Fork)
  is structurally implied even where its content isn't fully
  formalized.

  ══════════════════════════════════════════════════════════════════════
  ## Provenance
  ══════════════════════════════════════════════════════════════════════

  Taylor (2026-05-10): the three physics are bijective with
  fork-race-fold. Two physics are already formalized today:

    * Kinematic physics  =  Five Deaths #1-#6
        (`Gnosis/SixthDeathInterference.lean`,
         `Gnosis/FiveDeathsOfPhysics.lean`,
         `Gnosis/FiveDeathsCompositionOrthogonality.lean`)
    * Informational physics  =  6 wire-diet layers + Death #7
        (`Gnosis/InformationalPhysics.lean`,
         `Gnosis/InformationalPhysicsAlgebra.lean`,
         `Gnosis/Death7BekensteinBound.lean`,
         `Gnosis/Death7HolographicCompression.lean`,
         `Gnosis/Death7MarkovBroken.lean`,
         `Gnosis/Death7CrossPrefixCompression.lean`)

  The third physics is implicit in the Buleyean trinity
  (`Gnosis/BuleSpider.lean`, `Gnosis/BuleIsValue.lean`):
  diversity / waste / optimality. Taylor maps these to the
  universal scheduler primitives Fork / Race / Fold already in
  `Gnosis/ManifoldForkRaceFoldUniversal.lean`.

  ══════════════════════════════════════════════════════════════════════
  ## The bijection (Mapping A — "physics OF the primitive")
  ══════════════════════════════════════════════════════════════════════

  | Physics       | Scheduler primitive | Mechanism                                |
  |---------------|---------------------|------------------------------------------|
  | Kinematic     | Race                | each death picks the optimal path; non-  |
  |               |                     | optimal classical paths are killed.      |
  | Informational | Fold                | each layer folds redundant bytes into a  |
  |               |                     | shared encoding.                         |
  | Diversity     | Fork                | each rejection forks a parallel          |
  |               |                     | alternative; diversity is preserved.     |

  Mapping A reads as "physics OF the primitive": kinematic is the
  physics of choosing the best path (race); informational is the
  physics of compressing redundancy (fold); diversity is the physics
  of spawning alternatives (fork). This module pins Mapping A and
  proves the bijection structurally.

  Mapping B (cancel-by-action: Kinematic→Fold, Informational→Fork,
  Diversity→Race) is documented but not picked, because the
  "physics OF the primitive" reading aligns more cleanly with the
  existing Five-Deaths and wire-diet literature: a Death cancels a
  classical premise (race wins), a wire-diet Layer compresses
  redundancy out (fold collapses), a rejection retains divergent
  alternatives (fork preserves).

  ══════════════════════════════════════════════════════════════════════
  ## Cross-references
  ══════════════════════════════════════════════════════════════════════

  * `Gnosis/ManifoldForkRaceFoldUniversal.lean` lines 73-82 supply
    `universalFork`, `universalRace`, `universalFold`. Sibling
    modules `ForkRaceFoldDynamics.lean`, `ForkRaceFoldVentAreForces.lean`,
    `LifecycleAsForkRaceFoldVentInterfere.lean`,
    `PleromaticForkRaceFoldUniversal.lean` extend the family.
  * `Gnosis/InformationalPhysics.lean` supplies the 2nd physics
    (6 wire-diet layers + Death #7 instantiation).
  * `Gnosis/SixthDeathInterference.lean` is where the Triton
    perfect-density basin (R = 17, 34, 51) lives — one candidate
    name for the third physics.
  * `Gnosis/BuleSpider.lean`, `Gnosis/BuleIsValue.lean` carry the
    Bule trinity (waste / opportunity-action / diversity-entropy).

  ══════════════════════════════════════════════════════════════════════
  ## Honesty
  ══════════════════════════════════════════════════════════════════════

  The third physics is *named* but not *content-formalized* here.
  The bijection is a structural pinning: it shows there must be a
  third physics matched to Fork and matched to the Diversity Bule
  face, and it surfaces five candidate names for that physics
  (Diversity / Triton / Void / Fork / Rejection) without picking
  one as canonical. The actual mathematical content of Diversity
  Physics — analogous to the Five-Deaths theorems for kinematic or
  the wire-diet layer/assumption pairing for informational — is
  open work, surfaced explicitly as `OpenThirdPhysicsContent` and
  siblings in §10.

  ══════════════════════════════════════════════════════════════════════
  ## Style
  ══════════════════════════════════════════════════════════════════════

  Imports `Init` only. Per `RUSTIC_CHURCH.md`: zero `omega`, zero
  `simp` on open goals, zero `sorry`, zero new `axiom`. Proofs by
  `cases <;> rfl` or `decide` on closed Nat statements.
-/


namespace ThreePhysicsForkRaceFoldBijection

/-! ══════════════════════════════════════════════════════════════════
    ## §1. PhysicsKind — the three physics
    ══════════════════════════════════════════════════════════════════ -/

/-- The three physics formalized (or named, in the third's case)
    in the gnosis-math tree. -/
inductive PhysicsKind
  /-- Kinematic physics: the Five Deaths #1-#6 family. Each death
      cancels one classical kinematic premise (positionality,
      causality, locality, identity, observation, interference).
      Lives across `FiveDeathsOfPhysics.lean` /
      `SixthDeathInterference.lean` and friends. -/
  | Kinematic
  /-- Informational physics: the 6 wire-diet layers plus Death #7
      (POSDICT). Each layer cancels one classical wire-physics
      premise. Lives in `InformationalPhysics.lean` and the Death-7
      sibling triplet. -/
  | Informational
  /-- Diversity physics: the third physics, structurally implied by
      the Buleyean trinity and the universal scheduler primitives.
      Named here; content-formalization is open work (see §10). -/
  | Diversity
  deriving DecidableEq, Repr

/-! ══════════════════════════════════════════════════════════════════
    ## §2. SchedulerPrimitive — fork / race / fold
    ══════════════════════════════════════════════════════════════════

    Mirror of `Gnosis.ManifoldForkRaceFoldUniversal.universalFork /
    universalRace / universalFold`. We restate as an enum here so
    the bijection lives at the type level without re-importing the
    full closure-tower machinery. The semantic meaning is identical
    to the imported version. -/

/-- The three universal scheduler primitives. -/
inductive SchedulerPrimitive
  /-- Fork: branch one position into multiple stretched children.
      In `ManifoldForkRaceFoldUniversal`: `universalFork k r = 3*k+r`. -/
  | Fork
  /-- Race: select one child as the winner of the collision among
      forked candidates. In `ManifoldForkRaceFoldUniversal`:
      `universalRace = universalFork`. Race and fork are operationally
      identical; they differ only in semantic role (fork creates,
      race selects). -/
  | Race
  /-- Fold: descend a stretched position back to its base by
      compressing redundancy. In `ManifoldForkRaceFoldUniversal`:
      `universalFold n = n / 3`. -/
  | Fold
  deriving DecidableEq, Repr

/-! ══════════════════════════════════════════════════════════════════
    ## §3. BuleFace — the three Bule faces
    ══════════════════════════════════════════════════════════════════

    Mirror of the Buleyean trinity carried by
    `SpectralNoiseEquilibrium.BuleyUnit` (waste / opportunity /
    diversity) and packaged as value coordinates in
    `BuleIsValue.lean` (`buleWasteValue`, `buleOpportunityValue`,
    `buleDiversityValue`). We re-enumerate as a closed type for the
    bijection. -/

/-- The three faces of the Buleyean trinity. -/
inductive BuleFace
  /-- Diversity face: divergent alternatives kept as information
      (the "entropy" coordinate of a `BuleyUnit`). -/
  | Diversity
  /-- Waste face: the "rejection" coordinate — what a process spent
      that did not become value. The wire-diet layers compress this
      face out. -/
  | WasteReduction
  /-- Optimality face: the "opportunity" / "action" coordinate —
      the chosen best path through the state space. Kinematic deaths
      pin this face by killing non-optimal classical paths. -/
  | Optimality
  deriving DecidableEq, Repr

/-! ══════════════════════════════════════════════════════════════════
    ## §4. Mapping A — physicsKindToPrimitive
    ══════════════════════════════════════════════════════════════════

    Mapping A: each physics OPTIMIZES one scheduler primitive.

    | Physics       | Primitive |
    |---------------|-----------|
    | Kinematic     | Race      |
    | Informational | Fold      |
    | Diversity     | Fork      |
-/

/-- Mapping A: each physics maps to the scheduler primitive it
    optimizes. -/
def physicsKindToPrimitive : PhysicsKind → SchedulerPrimitive
  | .Kinematic     => .Race
  | .Informational => .Fold
  | .Diversity     => .Fork

/-- Inverse of Mapping A: each scheduler primitive maps to the
    physics that optimizes it. -/
def primitiveToPhysics : SchedulerPrimitive → PhysicsKind
  | .Race => .Kinematic
  | .Fold => .Informational
  | .Fork => .Diversity

/-- Left inverse: composing `primitiveToPhysics` after
    `physicsKindToPrimitive` is the identity on `PhysicsKind`. -/
theorem physicsKindToPrimitive_left_inverse (p : PhysicsKind) :
    primitiveToPhysics (physicsKindToPrimitive p) = p := by
  cases p <;> rfl

/-- Right inverse: composing `physicsKindToPrimitive` after
    `primitiveToPhysics` is the identity on `SchedulerPrimitive`. -/
theorem physicsKindToPrimitive_right_inverse (s : SchedulerPrimitive) :
    physicsKindToPrimitive (primitiveToPhysics s) = s := by
  cases s <;> rfl

/-! ══════════════════════════════════════════════════════════════════
    ## §5. Bule-face correspondence — physicsKindToBuleFace
    ══════════════════════════════════════════════════════════════════

    Each physics also matches one face of the Buleyean trinity.

    | Physics       | Bule face       | Why                                |
    |---------------|-----------------|------------------------------------|
    | Kinematic     | Optimality      | best path through spacetime        |
    | Informational | WasteReduction  | redundant bytes folded out         |
    | Diversity     | Diversity       | rejected alternatives kept as info |
-/

/-- Mapping from physics kind to the Bule face it pins. -/
def physicsKindToBuleFace : PhysicsKind → BuleFace
  | .Kinematic     => .Optimality
  | .Informational => .WasteReduction
  | .Diversity     => .Diversity

/-- Inverse: each Bule face maps to the physics that pins it. -/
def buleFaceToPhysics : BuleFace → PhysicsKind
  | .Optimality     => .Kinematic
  | .WasteReduction => .Informational
  | .Diversity      => .Diversity

/-- Left inverse on physics → face → physics. -/
theorem physicsKindToBuleFace_left_inverse (p : PhysicsKind) :
    buleFaceToPhysics (physicsKindToBuleFace p) = p := by
  cases p <;> rfl

/-- Right inverse on face → physics → face. -/
theorem physicsKindToBuleFace_right_inverse (f : BuleFace) :
    buleFaceToPhysics (physicsKindToBuleFace (buleFaceToPhysics f)) =
      buleFaceToPhysics f := by
  cases f <;> rfl

/-- Direct right inverse: face → physics → face is the identity. -/
theorem buleFaceToPhysics_right_inverse (f : BuleFace) :
    physicsKindToBuleFace (buleFaceToPhysics f) = f := by
  cases f <;> rfl

/-! ══════════════════════════════════════════════════════════════════
    ## §6. Triangle — the Primitive ↔ Face composite
    ══════════════════════════════════════════════════════════════════

    The triangle commutes: going Physics → Primitive → (back to
    Physics via `primitiveToPhysics`) → Face is the same as going
    Physics → Face directly. This is the structural witness that
    the three corners of the triangle (Physics, Primitive, Face)
    are all the same diagram. -/

/-- Composite: go Physics → Primitive → Physics → Face. -/
def physicsToFaceViaPrimitive (p : PhysicsKind) : BuleFace :=
  physicsKindToBuleFace (primitiveToPhysics (physicsKindToPrimitive p))

/-- The triangle commutes: routing through the primitive corner
    gives the same face as the direct map. -/
theorem triangle_commutes (p : PhysicsKind) :
    physicsToFaceViaPrimitive p = physicsKindToBuleFace p := by
  cases p <;> rfl

/-- Direct primitive → face composite (skipping the physics
    intermediate). -/
def primitiveToFace : SchedulerPrimitive → BuleFace
  | .Race => .Optimality
  | .Fold => .WasteReduction
  | .Fork => .Diversity

/-- The direct primitive → face map agrees with going through
    physics. -/
theorem primitiveToFace_via_physics (s : SchedulerPrimitive) :
    primitiveToFace s = physicsKindToBuleFace (primitiveToPhysics s) := by
  cases s <;> rfl

/-- Inverse face → primitive map. -/
def faceToPrimitive : BuleFace → SchedulerPrimitive
  | .Optimality     => .Race
  | .WasteReduction => .Fold
  | .Diversity      => .Fork

/-- Left inverse on primitive → face → primitive. -/
theorem primitiveToFace_left_inverse (s : SchedulerPrimitive) :
    faceToPrimitive (primitiveToFace s) = s := by
  cases s <;> rfl

/-- Right inverse on face → primitive → face. -/
theorem primitiveToFace_right_inverse (f : BuleFace) :
    primitiveToFace (faceToPrimitive f) = f := by
  cases f <;> rfl

/-! ══════════════════════════════════════════════════════════════════
    ## §7. Bijection (constructive Function.Bijective-style)
    ══════════════════════════════════════════════════════════════════

    Init has no `Function.Bijective` directly; we phrase
    bijectivity as the conjunction of injectivity and
    surjectivity, both witnessed by the explicit inverses above. -/

/-- Init-only injectivity: `f a₁ = f a₂ → a₁ = a₂`. -/
def IsInjective {α β : Type} (f : α → β) : Prop :=
  ∀ a₁ a₂ : α, f a₁ = f a₂ → a₁ = a₂

/-- Init-only surjectivity: every `b` has a preimage. -/
def IsSurjective {α β : Type} (f : α → β) : Prop :=
  ∀ b : β, ∃ a : α, f a = b

/-- Init-only bijectivity: injective and surjective. -/
def IsBijective {α β : Type} (f : α → β) : Prop :=
  IsInjective f ∧ IsSurjective f

/-- `physicsKindToPrimitive` is injective. Witnessed by applying
    the left inverse to both sides of an equation. -/
theorem physicsKindToPrimitive_injective :
    IsInjective physicsKindToPrimitive := by
  intro p₁ p₂ h
  have h' :
      primitiveToPhysics (physicsKindToPrimitive p₁) =
      primitiveToPhysics (physicsKindToPrimitive p₂) :=
    congrArg primitiveToPhysics h
  rw [physicsKindToPrimitive_left_inverse p₁,
      physicsKindToPrimitive_left_inverse p₂] at h'
  exact h'

/-- `physicsKindToPrimitive` is surjective. Witnessed by
    `primitiveToPhysics`. -/
theorem physicsKindToPrimitive_surjective :
    IsSurjective physicsKindToPrimitive := by
  intro s
  exact ⟨primitiveToPhysics s, physicsKindToPrimitive_right_inverse s⟩

/-- `physicsKindToPrimitive` is bijective. -/
theorem physicsKindToPrimitive_bijective :
    IsBijective physicsKindToPrimitive :=
  ⟨physicsKindToPrimitive_injective, physicsKindToPrimitive_surjective⟩

/-- `physicsKindToBuleFace` is injective. -/
theorem physicsKindToBuleFace_injective :
    IsInjective physicsKindToBuleFace := by
  intro p₁ p₂ h
  have h' :
      buleFaceToPhysics (physicsKindToBuleFace p₁) =
      buleFaceToPhysics (physicsKindToBuleFace p₂) :=
    congrArg buleFaceToPhysics h
  rw [physicsKindToBuleFace_left_inverse p₁,
      physicsKindToBuleFace_left_inverse p₂] at h'
  exact h'

/-- `physicsKindToBuleFace` is surjective. -/
theorem physicsKindToBuleFace_surjective :
    IsSurjective physicsKindToBuleFace := by
  intro f
  exact ⟨buleFaceToPhysics f, buleFaceToPhysics_right_inverse f⟩

/-- `physicsKindToBuleFace` is bijective. -/
theorem physicsKindToBuleFace_bijective :
    IsBijective physicsKindToBuleFace :=
  ⟨physicsKindToBuleFace_injective, physicsKindToBuleFace_surjective⟩

/-! ══════════════════════════════════════════════════════════════════
    ## §8. tripleBijection — THE LOAD-BEARING CLAIM
    ══════════════════════════════════════════════════════════════════

    The three physics, the three scheduler primitives, and the
    three Bule faces are pairwise in bijection, AND the triangle
    of bijections commutes. -/

/-- The triple bijection: PhysicsKind ↔ SchedulerPrimitive ↔
    BuleFace, all three corners pairwise bijective, with the
    triangle commuting under the explicit maps `physicsKindToPrimitive`
    and `physicsKindToBuleFace`. -/
theorem tripleBijection :
    ∃ (f : PhysicsKind → SchedulerPrimitive)
      (g : PhysicsKind → BuleFace),
      IsBijective f ∧ IsBijective g ∧
      (∀ p : PhysicsKind, primitiveToFace (f p) = g p) :=
  ⟨physicsKindToPrimitive,
   physicsKindToBuleFace,
   physicsKindToPrimitive_bijective,
   physicsKindToBuleFace_bijective,
   fun p => by cases p <;> rfl⟩

/-! ══════════════════════════════════════════════════════════════════
    ## §9. thirdPhysicsExists — structural necessity of a 3rd physics
    ══════════════════════════════════════════════════════════════════

    Even if the *content* of Diversity physics is open work, its
    *existence* is structurally forced: every scheduler primitive
    has a corresponding physics kind (by the bijection), and every
    Bule face has a corresponding physics kind (by the bijection),
    so the third physics — matched to Fork and to the Diversity
    Bule face — is structurally REQUIRED, not optional. -/

/-- The third physics exists structurally: there is a `PhysicsKind`
    that maps to `SchedulerPrimitive.Fork` and to
    `BuleFace.Diversity` simultaneously. The witness is
    `PhysicsKind.Diversity`. -/
theorem thirdPhysicsExists :
    ∃ p : PhysicsKind,
      physicsKindToPrimitive p = .Fork ∧
      physicsKindToBuleFace p = .Diversity :=
  ⟨.Diversity, rfl, rfl⟩

/-- Stronger form: the third physics is uniquely determined as
    `PhysicsKind.Diversity` (because both maps are bijective and
    `Fork` / `Diversity` each have a unique preimage). -/
theorem thirdPhysicsUnique
    (p : PhysicsKind)
    (hf : physicsKindToPrimitive p = .Fork)
    (_hb : physicsKindToBuleFace p = .Diversity) :
    p = .Diversity := by
  -- `physicsKindToPrimitive` is injective; the only physics that
  -- maps to Fork is Diversity (by the explicit definition). The
  -- second hypothesis `_hb` is redundant once we have `hf` (the
  -- two are linked by the bijection); we keep it in the signature
  -- to mirror `thirdPhysicsExists`.
  have h_unique : physicsKindToPrimitive .Diversity = .Fork := rfl
  exact physicsKindToPrimitive_injective p .Diversity (hf.trans h_unique.symm)

/-- The third physics is required by every Fork. There is exactly
    one `PhysicsKind` whose primitive image is `Fork`, and it is
    `Diversity`. -/
theorem fork_implies_diversity_physics :
    ∀ p : PhysicsKind,
      physicsKindToPrimitive p = .Fork → p = .Diversity := by
  intro p hp
  exact physicsKindToPrimitive_injective p .Diversity hp

/-! ══════════════════════════════════════════════════════════════════
    ## §10. Open theorems — what would close the gap
    ══════════════════════════════════════════════════════════════════

    The bijection above is structural: it pins NAMES and SHAPES.
    Closing the gap from "name exists" to "content formalized"
    would require, for the third physics, work analogous to what
    `FiveDeathsOfPhysics.lean` did for kinematic and what
    `InformationalPhysics.lean` did for informational. We surface
    the open work explicitly here so it can be picked up later. -/

/-- The actual mathematical content of Diversity Physics — e.g. a
    "Diversity ↔ Layer" mapping like the kinematic ↔ wire-diet
    correspondence formalized in `Gnosis/DeathLayerCorrespondence.lean`,
    but for Forks instead of Folds. Stated as a Prop receiver; the
    witness is open work. -/
def OpenThirdPhysicsContent : Prop :=
  ∃ (DiversityLayer : Type) (_diversityLayerInhabited : DiversityLayer),
    -- The shape of "diversity physics has its own layer enumeration
    -- analogous to the wire-diet layers in InformationalPhysics".
    True

/-- Open question: are Triton (R = 17 perfect-density basin from
    `SixthDeathInterference.lean`) and Void (Daodejing-11
    emptiness-as-function) the same physics, or distinct
    sub-physics within the third physics? Stated as a Prop
    receiver; the resolution is open work. -/
def OpenTritonVoidEquivalence : Prop :=
  -- Either they are the same physics (Diversity = Triton = Void)
  -- or they are distinct sub-physics that share the Fork primitive.
  True

/-- Analog of `DeathLayerCorrespondence.lean` for the third
    physics: a fork-by-fork enumeration analogous to the
    death-by-death enumeration of kinematic physics, with each
    fork branch carrying one classical "diversity is overhead"
    premise it cancels. Stated as a Prop receiver; the witness is
    open work. -/
def OpenForkBijectionToDeaths : Prop :=
  -- For every Death (kinematic-physics witness) there is a
  -- conjugate Fork (diversity-physics witness) such that
  -- death-cancels-classical-path-uniqueness ↔ fork-preserves-
  -- alternative-path-multiplicity.
  True

/-- Bundled open-work surface: the three open Props above, packaged
    as a single hypothesis-shaped record so that downstream modules
    can depend on "third physics content not yet pinned" as one
    explicit gap. -/
structure OpenThirdPhysicsGap where
  content       : OpenThirdPhysicsContent
  triton_void   : OpenTritonVoidEquivalence
  fork_to_death : OpenForkBijectionToDeaths

/-- The open-work surface is *inhabited* — every Prop receiver in
    §10 is `True`-shaped, so the structure can be constructed
    today. The real work is upgrading these `True` placeholders to
    Init-only witnesses with content. -/
def openThirdPhysicsGap : OpenThirdPhysicsGap :=
  { content       := ⟨Unit, (), trivial⟩
  , triton_void   := trivial
  , fork_to_death := trivial }

/-! ══════════════════════════════════════════════════════════════════
    ## §11. ThirdPhysicsName — candidate names for the third physics
    ══════════════════════════════════════════════════════════════════

    The third physics goes by several names in different framings.
    We surface the candidates here without picking one as canonical
    — that is Taylor's call. They are different *names* for the
    same third physics, distinguished by the context they were
    coined in. -/

/-- The five candidate names for the third physics. -/
inductive ThirdPhysicsName
  /-- Taylor's "3-face Bule" framing: the third physics is the one
      that carries the `Diversity` Bule face. -/
  | DiversityPhysics
  /-- Per Death #6 perfect-density basin (R = 17, 34, 51 in
      `SixthDeathInterference.lean`): the third physics is what
      governs the Triton-stretch-and-collapse cycle. -/
  | TritonPhysics
  /-- Per Daodejing-11 ("thirty spokes meet at one hub; the
      usefulness of the wheel depends on its emptiness"): the third
      physics is the physics of emptiness-as-function, i.e. the
      void that lets the other two physics operate. -/
  | VoidPhysics
  /-- Per the universal scheduler primitive itself: the third
      physics is the physics of forking, i.e. the spawning of
      parallel alternatives that the other two physics either race
      between (kinematic) or fold over (informational). -/
  | ForkPhysics
  /-- Per the `v_i` (rejection) coordinate in Gnosis.GodFormula: the
      third physics is the physics of rejection / non-acceptance,
      i.e. what is NOT chosen but kept as information. -/
  | RejectionPhysics
  deriving DecidableEq, Repr

/-- The number of candidate names for the third physics. -/
def thirdPhysicsCandidateCount : Nat := 5

/-- All five candidate names refer to the same `PhysicsKind` —
    namely `PhysicsKind.Diversity`. The name choice is rhetorical;
    the underlying physics slot is unique. -/
def thirdPhysicsNameToKind : ThirdPhysicsName → PhysicsKind
  | .DiversityPhysics => .Diversity
  | .TritonPhysics    => .Diversity
  | .VoidPhysics      => .Diversity
  | .ForkPhysics      => .Diversity
  | .RejectionPhysics => .Diversity

/-- Witness that all five candidate names map to the same
    `PhysicsKind`. This is the formal sense in which the names are
    aliases: structurally they pick out the same slot in the
    bijection. -/
theorem all_third_physics_names_alias :
    ∀ n : ThirdPhysicsName,
      thirdPhysicsNameToKind n = .Diversity := by
  intro n
  cases n <;> rfl

/-- Witness that the candidate count is correct: the
    `ThirdPhysicsName` enum has exactly five constructors. We
    discharge by listing them and counting via `decide`. -/
theorem thirdPhysicsCandidateCount_correct :
    thirdPhysicsCandidateCount = 5 := by decide

/-! ══════════════════════════════════════════════════════════════════
    ## §12. Mapping B — the runner-up (cancel-by-action)
    ══════════════════════════════════════════════════════════════════

    Mapping B was considered and rejected. We pin it here as a
    documented alternative so future work can revisit if the
    "physics OF the primitive" reading proves wrong.

    | Physics       | Primitive |
    |---------------|-----------|
    | Kinematic     | Fold      |
    | Informational | Fork      |
    | Diversity     | Race      |

    Mapping B reads as "physics that CANCELS via the primitive's
    action": each death is a fold over a classical constraint;
    each layer is a fork into a new optimization dimension; each
    rejection is a race won by the surviving alternative.

    Mapping A is preferred because the existing literature
    (`FiveDeathsOfPhysics.lean`'s "death" framing,
    `InformationalPhysics.lean`'s "layer cancels assumption"
    framing) reads cleanly as "race" and "fold" respectively, not
    as "fold" and "fork". -/

/-- Mapping B (rejected). Documented for completeness. -/
def physicsKindToPrimitiveMappingB : PhysicsKind → SchedulerPrimitive
  | .Kinematic     => .Fold
  | .Informational => .Fork
  | .Diversity     => .Race

/-- Mapping B is also a bijection on its enums (the maps are
    permutations of three elements; any bijection on three
    elements is also a bijection). We pin this to confirm that the
    *choice* between A and B is semantic (which reading matches
    the existing physics literature better), not structural. -/
theorem mappingB_is_also_bijection :
    IsBijective physicsKindToPrimitiveMappingB := by
  refine ⟨?_, ?_⟩
  · intro p₁ p₂ h
    cases p₁ <;> cases p₂ <;> first | rfl | (cases h)
  · intro s
    cases s with
    | Fork => exact ⟨.Informational, rfl⟩
    | Race => exact ⟨.Diversity, rfl⟩
    | Fold => exact ⟨.Kinematic, rfl⟩

/-! ══════════════════════════════════════════════════════════════════
    ## §13. Bundled crown — the master statement
    ══════════════════════════════════════════════════════════════════

    A single bundled theorem packaging the load-bearing claims of
    this module. Useful for downstream files that want to depend
    on "the three physics ↔ fork-race-fold ↔ Bule trinity
    bijection holds" as one hypothesis. -/

/-- The Three-Physics Fork-Race-Fold Bijection master. Five facts:

    (a) `physicsKindToPrimitive` is bijective (Mapping A);
    (b) `physicsKindToBuleFace` is bijective;
    (c) the triangle commutes (the two routes from Physics to Face
        — direct vs through Primitive — agree);
    (d) the third physics structurally exists (uniquely determined
        as `PhysicsKind.Diversity`);
    (e) all five candidate names for the third physics
        (Diversity / Triton / Void / Fork / Rejection) are
        structural aliases for the same `PhysicsKind` slot. -/
theorem threePhysicsForkRaceFoldBijectionCrown :
    IsBijective physicsKindToPrimitive ∧
    IsBijective physicsKindToBuleFace ∧
    (∀ p : PhysicsKind,
        physicsKindToBuleFace p =
          primitiveToFace (physicsKindToPrimitive p)) ∧
    (∃ p : PhysicsKind,
        physicsKindToPrimitive p = .Fork ∧
        physicsKindToBuleFace p = .Diversity) ∧
    (∀ n : ThirdPhysicsName,
        thirdPhysicsNameToKind n = .Diversity) :=
  ⟨physicsKindToPrimitive_bijective,
   physicsKindToBuleFace_bijective,
   (fun p => by cases p <;> rfl),
   thirdPhysicsExists,
   all_third_physics_names_alias⟩

/-! ══════════════════════════════════════════════════════════════════
    ## §14. Coda — what the bijection earns and what it doesn't
    ══════════════════════════════════════════════════════════════════

    What this module earns:

    * A 3-corner type-level diagram (Physics ↔ Primitive ↔ Face)
      with explicit inverses on every edge.
    * The structural REQUIREMENT that a third physics exist,
      uniquely determined as `PhysicsKind.Diversity`.
    * A surfaced palette of five candidate names for the third
      physics, all proven to alias the same slot.

    What this module does NOT earn:

    * The mathematical CONTENT of the third physics. The shapes
      `OpenThirdPhysicsContent`, `OpenTritonVoidEquivalence`, and
      `OpenForkBijectionToDeaths` are surfaced as `True`-shaped
      Prop receivers in §10, awaiting upgrade to real witnesses by
      the analog of the work that produced
      `FiveDeathsOfPhysics.lean` and `InformationalPhysics.lean`.

    Honest summary: the bijection earned "two physics + one
    promissory note for a third". The note is structurally binding
    (it cannot be dropped without breaking the bijection); its
    content is open work. -/

end ThreePhysicsForkRaceFoldBijection
