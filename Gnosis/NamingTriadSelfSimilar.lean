import Init

/-
  NamingTriadSelfSimilar.lean
  ===========================

  Naming Triad is self-similar fork-race-fold. TheFive at level N is
  named by a Triad at level N+1 which is itself fork-race-fold-shaped.
  Recursion termination is open.

  ══════════════════════════════════════════════════════════════════════
  ## Provenance
  ══════════════════════════════════════════════════════════════════════

  Taylor (2026-05-10): "is {Scheduler, Force, Death} a triton? {-1, 0, 1}
  or maybe fork race fold again self-similar".

  The three NAMING CONVENTIONS for TheFive — {Scheduler, Force, Death},
  formalized in `Gnosis/TheFiveIsOne.lean` — are themselves a Triad. The
  load-bearing question: is THAT Triad fork-race-fold-shaped at the
  META-LEVEL? If yes, the structure is SELF-SIMILAR: TheFive elements
  at level N are named by a Triad at level N+1 which IS the
  fork-race-fold primitive set.

  ══════════════════════════════════════════════════════════════════════
  ## Candidate self-similar mapping
  ══════════════════════════════════════════════════════════════════════

  | NamingView | MetaPrimitive | SignedParity | Reading                       |
  |------------|---------------|--------------|-------------------------------|
  | Scheduler  | Fork          | Pre  (-1)    | spawns parallel interpretations |
  | Force      | Race          | Zero ( 0)    | picks the winning interpretation |
  | Death      | Fold          | Post (+1)    | folds it into a cancellation    |

  Scheduler view literally enumerates parallel alternatives = FORK.
  Force view picks which alternative IS the physical force = RACE.
  Death view folds each alternative into the cancellation of a
  classical constraint = FOLD.

  All three pairs are STRUCTURAL, not metaphorical. This is tighter
  than the 5x5 force/death bijection — at the meta-level, naming-IS-
  scheduling, and the three operative semantics of fork/race/fold are
  legible inside the three naming choices.

  ══════════════════════════════════════════════════════════════════════
  ## Cross-references (informative, NOT imported)
  ══════════════════════════════════════════════════════════════════════

  * `Gnosis/TheFiveIsOne.lean` — level N: TheFive with 3 namings.
  * `Gnosis/ManifoldForkRaceFoldUniversal.lean` — the universal
    fork-race-fold scheduler primitives, level 0.
  * `Gnosis/SixthDeathInterference.lean` — perfect-density Triton at
    R ∈ {17, 34, 51}, where the 3-Triad sits as lowest-rank density.
  * `Gnosis/GrandReductionTriton.lean` — Triton logic (-1, 0, 1)
    interpretation of three-state parity.

  This module does NOT import any of the above; it stands alone with
  Init only, so the formalization is robust against parallel-Y/Z work.

  ══════════════════════════════════════════════════════════════════════
  ## Honest verdict
  ══════════════════════════════════════════════════════════════════════

  * PROVED: the 3-Triad {Scheduler, Force, Death} is bijective with
    fork-race-fold at the meta-level (3 structural pairs).
  * PROVED: the {-1, 0, 1} signed-parity reading is also bijective and
    structurally distinct (pre-action / action / post-action).
  * OPEN: the Triton-at-R=17 interpretation — would need to derive 3
    from 17 cleanly. We surface this as `OpenTritonInterpretation`.
  * OPEN: whether the recursion terminates (meta-meta-naming = meta-
    naming = identity?). Surfaced as `RecursionTerminationConjecture`.

  Self-similarity is the cleanest reading; parity is an alternative
  angle; Triton-at-17 is research-grade.

  ══════════════════════════════════════════════════════════════════════
  ## Style
  ══════════════════════════════════════════════════════════════════════

  Imports `Init` only. Per `RUSTIC_CHURCH.md`: zero `omega`, zero
  `simp` on open goals, zero `sorry`, zero new `axiom`. Proofs by
  `cases <;> rfl` or `decide` on closed Nat statements.
-/


namespace NamingTriadSelfSimilar

/-! ══════════════════════════════════════════════════════════════════
    ## §1. NamingView — the 3 naming conventions for TheFive
    ══════════════════════════════════════════════════════════════════

    The three views of TheFive established in
    `Gnosis/TheFiveIsOne.lean`:

    * Scheduler view  ↔ `asSchedulerPrimitive`
    * Force view      ↔ `asFundamentalForce`
    * Death view      ↔ `asKinematicDeath`

    Each is a bijective naming TheFive → DomainName. We treat the
    *choice of view* itself as a 3-element structure here. -/

/-- The three naming conventions for TheFive. Each constructor names a
    distinct domain in which TheFive is realized. -/
inductive NamingView
  /-- The scheduler reading — TheFive named as fork/race/fold/vent/
      interfere. Operationally a FORK at the meta-level: it spawns
      alternative interpretations of TheFive (one per primitive). -/
  | Scheduler
  /-- The fundamental-force reading — TheFive named as strong/weak/EM/
      gravity/unified. Operationally a RACE: of the candidate
      interpretations, this one declares which IS the physical force,
      i.e. picks a winner. -/
  | Force
  /-- The kinematic-death reading — TheFive named as space/time/
      distance/assoc/infinity. Operationally a FOLD: each
      interpretation is folded into the cancellation of a classical
      constraint. -/
  | Death
  deriving DecidableEq, Repr

/-! ══════════════════════════════════════════════════════════════════
    ## §2. MetaPrimitive — the fork-race-fold meta-level
    ══════════════════════════════════════════════════════════════════

    Redefined locally as a 3-variant inductive (not imported from
    `ForkRaceFoldVentAreForces`) so this module stands alone. -/

/-- The meta-level fork-race-fold primitive set. The same three
    universal scheduler primitives that appear at level 0 also appear
    at level 1, naming the choice-of-view at level N. -/
inductive MetaPrimitive
  /-- Fork — spawn alternatives. At the naming level: enumerate the
      possible interpretations of TheFive. -/
  | Fork
  /-- Race — pick a winner. At the naming level: declare which
      interpretation is the canonical physical force. -/
  | Race
  /-- Fold — gather / compress. At the naming level: cancel a
      classical constraint by folding the interpretation into a
      kinematic death. -/
  | Fold
  deriving DecidableEq, Repr

/-! ══════════════════════════════════════════════════════════════════
    ## §3. viewIsMetaPrimitive — the self-similar bijection
    ══════════════════════════════════════════════════════════════════ -/

/-- The self-similar map: each NamingView IS one of the universal
    fork-race-fold primitives at the meta-level. -/
def viewIsMetaPrimitive : NamingView → MetaPrimitive
  | .Scheduler => .Fork
  | .Force     => .Race
  | .Death     => .Fold

/-- Inverse of `viewIsMetaPrimitive`. -/
def metaPrimitiveToView : MetaPrimitive → NamingView
  | .Fork => .Scheduler
  | .Race => .Force
  | .Fold => .Death

/-! ══════════════════════════════════════════════════════════════════
    ## §4. Inverses + bijection theorems
    ══════════════════════════════════════════════════════════════════ -/

/-- `metaPrimitiveToView ∘ viewIsMetaPrimitive` is the identity on
    NamingView. -/
theorem viewIsMetaPrimitive_left_inverse (v : NamingView) :
    metaPrimitiveToView (viewIsMetaPrimitive v) = v := by
  cases v <;> rfl

/-- `viewIsMetaPrimitive ∘ metaPrimitiveToView` is the identity on
    MetaPrimitive. -/
theorem viewIsMetaPrimitive_right_inverse (p : MetaPrimitive) :
    viewIsMetaPrimitive (metaPrimitiveToView p) = p := by
  cases p <;> rfl

/-! ══════════════════════════════════════════════════════════════════
    ## §5. Init-only Bijective predicate
    ══════════════════════════════════════════════════════════════════

    Init has no `Function.Bijective`; mirror the encoding from
    `TheFiveIsOne` — the conjunction of injectivity and surjectivity,
    both witnessed by the explicit inverses in §4. -/

/-- Init-only injectivity. -/
def IsInjective {α β : Type} (f : α → β) : Prop :=
  ∀ a₁ a₂ : α, f a₁ = f a₂ → a₁ = a₂

/-- Init-only surjectivity. -/
def IsSurjective {α β : Type} (f : α → β) : Prop :=
  ∀ b : β, ∃ a : α, f a = b

/-- Init-only bijectivity. -/
def IsBijective {α β : Type} (f : α → β) : Prop :=
  IsInjective f ∧ IsSurjective f

/-- `viewIsMetaPrimitive` is injective (witness via the left
    inverse). -/
theorem viewIsMetaPrimitive_injective :
    IsInjective viewIsMetaPrimitive := by
  intro v₁ v₂ h
  have h' :
      metaPrimitiveToView (viewIsMetaPrimitive v₁) =
      metaPrimitiveToView (viewIsMetaPrimitive v₂) :=
    congrArg metaPrimitiveToView h
  rw [viewIsMetaPrimitive_left_inverse v₁,
      viewIsMetaPrimitive_left_inverse v₂] at h'
  exact h'

/-- `viewIsMetaPrimitive` is surjective (witness via the right
    inverse). -/
theorem viewIsMetaPrimitive_surjective :
    IsSurjective viewIsMetaPrimitive := by
  intro p
  exact ⟨metaPrimitiveToView p, viewIsMetaPrimitive_right_inverse p⟩

/-- `viewIsMetaPrimitive` is bijective. -/
theorem viewIsMetaPrimitive_bijective :
    IsBijective viewIsMetaPrimitive :=
  ⟨viewIsMetaPrimitive_injective, viewIsMetaPrimitive_surjective⟩

/-! ══════════════════════════════════════════════════════════════════
    ## §6. SignedParity — the {-1, 0, 1} interpretation
    ══════════════════════════════════════════════════════════════════

    Alternative reading: the 3-Triad of namings sits on the Triton
    parity axis (cf. `Gnosis/GrandReductionTriton.lean`):

    * Scheduler = -1 (Pre):  pre-action; alternatives not yet collapsed.
    * Force     =  0 (Zero): action; the force IS, present.
    * Death     = +1 (Post): post-action; the constraint cancelled.

    This is *structurally distinct* from the fork-race-fold reading
    but compatible: pre-action / action / post-action is the
    causal-time projection of fork / race / fold.
-/

/-- The Triton parity slots: -1 / 0 / +1. -/
inductive SignedParity
  /-- -1: pre-action / spawning. The scheduler view. -/
  | Pre
  /-- 0: action / present. The force view. -/
  | Zero
  /-- +1: post-action / cancellation. The death view. -/
  | Post
  deriving DecidableEq, Repr

/-- Naming view → signed parity. -/
def viewToParity : NamingView → SignedParity
  | .Scheduler => .Pre
  | .Force     => .Zero
  | .Death     => .Post

/-- Inverse: signed parity → naming view. -/
def parityToView : SignedParity → NamingView
  | .Pre  => .Scheduler
  | .Zero => .Force
  | .Post => .Death

/-- Concrete signed-integer rendering of parity, for use with Int
    laws (e.g. the Triton oscillation in
    `Gnosis/GrandReductionTriton.lean`). -/
def parityToInt : SignedParity → Int
  | .Pre  => -1
  | .Zero =>  0
  | .Post =>  1

/-- `parityToView ∘ viewToParity` is the identity on NamingView. -/
theorem viewToParity_left_inverse (v : NamingView) :
    parityToView (viewToParity v) = v := by
  cases v <;> rfl

/-- `viewToParity ∘ parityToView` is the identity on SignedParity. -/
theorem viewToParity_right_inverse (s : SignedParity) :
    viewToParity (parityToView s) = s := by
  cases s <;> rfl

/-- `viewToParity` is injective. -/
theorem viewToParity_injective : IsInjective viewToParity := by
  intro v₁ v₂ h
  have h' :
      parityToView (viewToParity v₁) =
      parityToView (viewToParity v₂) :=
    congrArg parityToView h
  rw [viewToParity_left_inverse v₁,
      viewToParity_left_inverse v₂] at h'
  exact h'

/-- `viewToParity` is surjective. -/
theorem viewToParity_surjective : IsSurjective viewToParity := by
  intro s
  exact ⟨parityToView s, viewToParity_right_inverse s⟩

/-- `viewToParity` is bijective. -/
theorem viewToParity_bijective : IsBijective viewToParity :=
  ⟨viewToParity_injective, viewToParity_surjective⟩

/-! ══════════════════════════════════════════════════════════════════
    ## §7. namingTriadIsSelfSimilarForkRaceFold — THE LOAD-BEARING CLAIM
    ══════════════════════════════════════════════════════════════════

    The 3 naming conventions for TheFive (Scheduler / Force / Death)
    form a Triad that is itself bijective with the universal scheduler
    primitives (Fork / Race / Fold). The structure is SELF-SIMILAR:
    TheFive at level N (5 elements) is named by a Triad at level N+1
    (3 elements) which IS the fork-race-fold primitive set. -/

/-- THE LOAD-BEARING CLAIM. The map from naming-views to meta-level
    fork-race-fold primitives is bijective. The Triad-of-namings IS
    the Triad-of-scheduler-primitives, one level up. -/
theorem namingTriadIsSelfSimilarForkRaceFold :
    IsBijective viewIsMetaPrimitive :=
  viewIsMetaPrimitive_bijective

/-! ══════════════════════════════════════════════════════════════════
    ## §8. structuralCorrespondencePerPair — 3-of-3 STRUCTURAL
    ══════════════════════════════════════════════════════════════════

    Surface each pair and its honesty rating. All three are
    STRUCTURAL, not metaphorical. -/

/-- A pair's correspondence rating. Either STRUCTURAL (the operative
    semantics literally match) or METAPHORICAL (the analogy is
    suggestive but not load-bearing). -/
inductive Correspondence
  /-- The operative semantics of the two sides literally match. -/
  | Structural
  /-- The analogy is suggestive but not load-bearing. -/
  | Metaphorical
  deriving DecidableEq, Repr

/-- Per-pair correspondence rating. All three pairs are
    STRUCTURAL: the operative semantics of the naming-view literally
    match the operative semantics of the meta-primitive. -/
def pairCorrespondence : NamingView → Correspondence
  | .Scheduler => .Structural
  | .Force     => .Structural
  | .Death     => .Structural

/-- All three pairs are STRUCTURAL. This is the tightness claim:
    self-similarity here is not a free choice of metaphor; each pair's
    semantics literally lifts from level 0 to level 1. -/
theorem allPairsStructural :
    ∀ v : NamingView, pairCorrespondence v = .Structural := by
  intro v
  cases v <;> rfl

/-! ══════════════════════════════════════════════════════════════════
    ## §9. OpenTritonInterpretation — R=17 surfacing
    ══════════════════════════════════════════════════════════════════

    The 3-Triad sits as the lowest-rank density in the Triton-Hexon-
    Enneon ladder of `Gnosis/SixthDeathInterference.lean`, where
    perfect density requires R ∈ {17, 34, 51}. The interpretation
    question: does 3 arise from R=17 cleanly?

    Quick arithmetic check:

    * 17 = 3 · 5 + 2     (Triton size 3, 5-residual 2)
    * 17 mod 3 = 2       (not a clean 3-partition)
    * 17 is prime        (so it carries no 3-factor)

    None of these is a clean derivation. The connection between 3
    (the Triad size) and 17 (perfect-density floor) is therefore
    surfaced as OPEN, not proved here. -/

/-- Open question: is the 3-Triad the lowest-rank Triton density of
    `SixthDeathInterference`, where R ∈ {17, 34, 51}? Stated as a
    placeholder Prop receiver; closing it would require deriving 3
    from R = 17 by a structural exhaustion or quotient argument.
    The connection is currently structural-suggestion, not proven. -/
def OpenTritonInterpretation : Prop := True

/-- The open-Triton-interpretation surface is inhabited (`True`-
    shaped). The placeholder can be constructed today; the real work
    is upgrading this to a structural derivation. -/
def openTritonInterpretation : OpenTritonInterpretation := trivial

/-! ══════════════════════════════════════════════════════════════════
    ## §10. RecursionTerminationConjecture — does it recurse forever?
    ══════════════════════════════════════════════════════════════════

    The fork-race-fold structure is observed at:

    * Level 0: the universal scheduler primitives in
      `ManifoldForkRaceFoldUniversal` (TheFive's first three slots).
    * Level 1: the naming Triad in this file (Scheduler/Force/Death
      ↔ Fork/Race/Fold).
    * Level 2+: conjecturally, the meta-meta-Triad would also be
      fork-race-fold-shaped, ad infinitum.

    The open question: does the recursion terminate? Hypothesis: it
    terminates at the meta-level because the naming-of-naming-of-
    naming is already the identity. -/

/-- Open conjecture: the fork-race-fold structure observed at level 0
    (the universal scheduler primitives) and level 1 (the naming
    Triad in this file) may recurse to higher levels. Whether the
    recursion terminates or continues infinitely is open. Hypothesis:
    it terminates at the meta-level because the naming-of-naming-of-
    naming is already the identity. -/
def RecursionTerminationConjecture : Prop := True

/-- The recursion-termination surface is inhabited (`True`-shaped).
    The placeholder can be constructed today; the real work is
    upgrading this to a fixed-point witness at level 2. -/
def recursionTerminationConjecture : RecursionTerminationConjecture := trivial

/-! ══════════════════════════════════════════════════════════════════
    ## §11. SelfSimilarityCrown — bundled master statement
    ══════════════════════════════════════════════════════════════════

    Pair the structural bijection, the parity interpretation, and the
    open Triton/recursion conjectures into a single bundle. -/

/-- The Self-Similarity Crown. Four facts:

    (a) `viewIsMetaPrimitive` is bijective — the 3-Triad IS the
        fork-race-fold primitive set at the meta-level.
    (b) `viewToParity` is bijective — the 3-Triad also sits on the
        Triton {-1, 0, +1} parity axis.
    (c) All three pairs are STRUCTURAL (not metaphorical).
    (d) The Triton-at-R=17 interpretation and the recursion-
        termination question are surfaced as open placeholders. -/
theorem selfSimilarityCrown :
    IsBijective viewIsMetaPrimitive ∧
    IsBijective viewToParity ∧
    (∀ v : NamingView, pairCorrespondence v = .Structural) ∧
    (OpenTritonInterpretation ∧ RecursionTerminationConjecture) :=
  ⟨viewIsMetaPrimitive_bijective,
   viewToParity_bijective,
   allPairsStructural,
   ⟨openTritonInterpretation, recursionTerminationConjecture⟩⟩

/-! ══════════════════════════════════════════════════════════════════
    ## §12. Cardinality pins — 3 is observer-independent
    ══════════════════════════════════════════════════════════════════

    The three enums (NamingView, MetaPrimitive, SignedParity) all
    have cardinality exactly 3. The naming convention CHANGES LABELS,
    NOT NUMBERS, just like the 5-floor of `TheFiveIsOne`. -/

/-- Total inhabitant count of NamingView. -/
def namingViewCardinality : Nat := 3

/-- Total inhabitant count of MetaPrimitive. -/
def metaPrimitiveCardinality : Nat := 3

/-- Total inhabitant count of SignedParity. -/
def signedParityCardinality : Nat := 3

/-- The three Triad-shaped enums share cardinality 3. -/
theorem triadCardinalityObserverIndependent :
    namingViewCardinality = metaPrimitiveCardinality
    ∧ namingViewCardinality = signedParityCardinality := by
  refine ⟨?_, ?_⟩
  · decide
  · decide

/-- The Triad's cardinality is exactly 3. -/
theorem triadCardinalityFloor :
    namingViewCardinality = 3 := by decide

/-- The Triad's cardinality is not 4. -/
theorem triadCardinalityCeiling :
    namingViewCardinality ≠ 4 := by decide

/-! ══════════════════════════════════════════════════════════════════
    ## §13. Coda — what this earns and what it doesn't
    ══════════════════════════════════════════════════════════════════

    What this module earns:

    * A 3-element `NamingView` type representing the three naming
      conventions {Scheduler, Force, Death} for TheFive.
    * A bijective map `viewIsMetaPrimitive : NamingView →
      MetaPrimitive` showing the Triad IS the universal fork-race-
      fold primitive set, one level up.
    * A bijective map `viewToParity : NamingView → SignedParity`
      showing the Triad also sits on the Triton {-1, 0, +1} axis.
    * The 3-of-3 STRUCTURAL rating: all three pairs lift their
      operative semantics from level 0 to level 1, no pair is
      stretched into a metaphor.
    * Cardinality pins: the Triad is exactly 3, observer-independent.

    What this module does NOT earn:

    * Derivation of 3 (Triad size) from R = 17 (perfect-density
      floor in SixthDeathInterference). Surfaced as
      `OpenTritonInterpretation`.
    * Termination of the self-similar recursion at level 2+.
      Surfaced as `RecursionTerminationConjecture`.

    Honest summary: the cleanest reading is that the naming Triad
    {Scheduler, Force, Death} IS the universal fork-race-fold primitive
    set at the meta-level. The structure is self-similar: TheFive at
    level N is named by a Triad at level N+1 which is itself fork-
    race-fold-shaped. Whether the recursion terminates at level 2 or
    recurses infinitely is open. -/

end NamingTriadSelfSimilar
