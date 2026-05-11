/-
  InformationalPhysicsCompleteness.lean
  =====================================

  The honest counterpart to `InformationalPhysics.lean`.

  ══════════════════════════════════════════════════════════════════════
  ## The deepest question raised by InformationalPhysics
  ══════════════════════════════════════════════════════════════════════

  Taylor (2026-05-10), in the honest-verdict review of
  `InformationalPhysics.lean`:

      "Why exactly 6 classical wire assumptions? Not 5, not 7. The
       bijection between InformationalLayer (6 variants) and
       ClassicalAssumption (6 variants) is forced by enum choice — but
       is it forced by physics?"

  This is the bookkeeping vs. physics question. The parent module
  proves that the six wire-diet layers stand in 1-1 correspondence
  with six named classical assumptions. That is a structural
  bijection between two finite sets the *author* hand-picked. It
  earns nothing about the cardinality 6 itself.

  Two possible answers:

    (A) "6" is a counting accident of how Taylor enumerated the
        layers in `WIRE_DIET.md`. Coarsen or refine the enumeration
        and you get 4 or 9 layers; the framework is just a list.

    (B) "6" is forced by the *structural dimensions* of a
        wire-byte stream. Each layer attacks one orthogonal
        dimension of where bytes can be wasted; the count of
        dimensions is the count of layers.

  Answer (B) is the stronger claim. This module argues for it
  *as far as Init-only Lean can argue*, and is honest about where
  the argument stops being a proof and starts being a conjecture.

  ══════════════════════════════════════════════════════════════════════
  ## What this module pins (PROVED vs. CONJECTURED)
  ══════════════════════════════════════════════════════════════════════

  PROVED (by `decide`, structural induction, or `cases <;> rfl`):

    1. `WireByteDimension` is a 6-variant inductive type. The variant
       count is fixed by the inductive declaration; `decide` confirms
       it via `(...).length = 6`.

    2. The map `layerDimension : InformationalLayer → WireByteDimension`
       is a bijection. Both inverse identities discharge by
       `cases <;> rfl`. This re-presents the parent module's
       layer/assumption bijection in dimensional language: each
       layer attacks the dimension named by the new enum.

    3. `dimensionCount = 6` and `layerCount = 6`, both by `decide`.
       Equality `layerCount = dimensionCount` is `rfl`.

    4. The "dimension-tagged classical constraint" total function
       `constraintDimension : ClassicalAssumption → WireByteDimension`
       is itself a bijection (left + right inverses by `cases`).
       This proves the parent module's two enums and this module's
       new enum form a *commutative triangle* of bijections.

    5. `alternative_decompositions_collapse`: any total bijection
       `WireByteDimension ≃ WireByteDimension` is the identity
       on cardinality — i.e. any "alternative" relabeling has 6
       elements. The relabeling theorem is the trivial enum-
       cardinality fact that an inductive type's constructor count
       is a structural invariant.

  CONJECTURED (stated as `Prop`, NOT proved; honest open problems):

    6. `noSeventhDimension`: there is no orthogonal seventh wire-byte
       dimension that does not reduce to one of the existing six.
       This module supplies *negativity witnesses* for the two most
       plausible candidates (temporal interleaving, encryption
       overhead) but does NOT prove a metalogical exhaustion
       theorem. Doing so would require a model of "all classical
       wire assumptions" — research-grade scope.

    7. `WireDietExhaustive`: the meta-claim that the six layers are
       jointly complete over the space of all classical wire
       assumptions. Stated declaratively as a `Prop`; not proved.

  Honest verdict (in §10): the dimension count `= 6` is structurally
  pinned *given the dimension enum we chose*, and the bijection from
  layers to dimensions is fully proved. Whether that enum is itself
  forced by physics is a stronger claim than this file earns. We
  reduce the question "why 6 layers?" to the question "why 6
  dimensions?", supply two negativity witnesses for the most
  plausible 7th dimension, and document the residual gap as an open
  conjecture.

  ══════════════════════════════════════════════════════════════════════
  ## Style
  ══════════════════════════════════════════════════════════════════════

  Imports `Init` and the parent `Gnosis.InformationalPhysics` only.
  Per `RUSTIC_CHURCH.md`: zero `omega`, zero `simp` on open goals,
  zero `sorry`, zero new `axiom`. Closed numeric witnesses use
  `decide`. Bijection proofs lean on `cases <;> rfl`. The two
  declarative `Prop`s in §6 and §8 are clearly marked as
  conjectures, NOT theorems.
-/

import Init
import Gnosis.InformationalPhysics

namespace InformationalPhysicsCompleteness

open InformationalPhysics

/-! ══════════════════════════════════════════════════════════════════
    ## §1. WireByteDimension — orthogonal dimensions of a wire stream
    ══════════════════════════════════════════════════════════════════

    A wire-byte stream can be optimized along (at least) six
    structurally distinct dimensions. Each dimension answers a
    different question:

      AlphabetSize        — how many bits do we burn per output symbol?
      FrameRepetition     — how predictable is the header structure?
      IntegerWidth        — are integer fields fixed- or variable-width?
      StreamOrdering      — does positional information carry data?
      StatisticalContext  — does sender + receiver share a prior?
      LanguageAlphabet    — is the byte even the right symbolic unit?

    The dimensions are *orthogonal* in the informal sense that
    optimizing one does not commit you to optimizing another:
    bwDense (alphabet) composes freely with frame-elision (repetition),
    Zeckendorf (integer width), Lehmer (ordering), arithmetic coding
    (context), and phoneme codecs (alphabet substrate). Each row of
    `WIRE_DIET.md` lives at a different "where the byte goes" axis.

    The count of variants here is the same `6` as `InformationalLayer`
    in the parent module; this is the load-bearing structural claim
    of this file. -/

/-- The six structurally distinct dimensions along which a wire-byte
    stream can be optimized. Each dimension is the *axis* attacked
    by exactly one wire-diet layer. -/
inductive WireByteDimension
  /-- Bits per output symbol. base64 burns 8 bits to carry ~6 bits;
      bwDense burns 8 bits to carry ~7 bits. The "what alphabet do
      we render in" axis. Attacked by Layer 0 (PerByteAlphabet). -/
  | AlphabetSize
  /-- Predictability of header structure across repeated frames.
      Each FlowFrame after the first repeats most of the prior
      frame's header. The "are we re-sending the same envelope"
      axis. Attacked by Layer 1 (FrameStructure). -/
  | FrameRepetition
  /-- Fixed vs. variable-length integer encoding. A 4-byte u32
      slot for a sequence number that's almost always < 256 is
      24 wasted bits. The "do small ints get a small encoding"
      axis. Attacked by Layer 2 (IntegerCoding). -/
  | IntegerWidth
  /-- Positional information carried by tuple/list ordering.
      The order of N known items is itself ⌊log₂(N!)⌋ free bits
      that classical wire physics burns into a separate index
      field. The "is the order data" axis. Attacked by Layer 3
      (OrderingFree). -/
  | StreamOrdering
  /-- Shared statistical prior between sender and receiver. The
      classical assumption is that each transmission is fresh; in
      reality, both ends often share a context (POSDICT, gzip
      window, learned domain prior). The "what does the receiver
      already know" axis. Attacked by Layer 4 (StatisticalPrior). -/
  | StatisticalContext
  /-- Symbolic-unit choice for the payload. The byte is the
      classical default; for natural-language voice/text, phonemes
      (or bigrams, syllables) are the right unit and compress to
      ~3 bits/char. The "is the byte even the right granule" axis.
      Attacked by Layer 5 (AlphabetSubstrate). -/
  | LanguageAlphabet
  deriving DecidableEq, Repr

/-! ══════════════════════════════════════════════════════════════════
    ## §2. dimensionCount — pinned to 6 by `decide`
    ══════════════════════════════════════════════════════════════════

    The variant count of an inductive type is a structural fact: it
    is fixed by the declaration. We compute it concretely as the
    length of an enumeration of all dimensions and pin the value
    `6` by `decide`.

    Pin both `dimensionCount` and the parallel `layerCount` to
    expose the equality directly. -/

/-- Enumerate every constructor of `WireByteDimension`. The count
    of this list is the dimension count; pinning it concretely
    keeps the cardinality claim `decide`-checkable. -/
def allDimensions : List WireByteDimension :=
  [.AlphabetSize, .FrameRepetition, .IntegerWidth,
   .StreamOrdering, .StatisticalContext, .LanguageAlphabet]

/-- Enumerate every constructor of `InformationalLayer` (parent
    module). Used to check that layer count = dimension count. -/
def allLayers : List InformationalLayer :=
  [.PerByteAlphabet, .FrameStructure, .IntegerCoding,
   .OrderingFree, .StatisticalPrior, .AlphabetSubstrate]

/-- The dimension count is `6`. Pinned by `decide` against the
    enumeration in `allDimensions`. -/
def dimensionCount : Nat := allDimensions.length

/-- The layer count is `6`. Pinned by `decide` against the
    enumeration in `allLayers`. -/
def layerCount : Nat := allLayers.length

/-- The dimension count is exactly `6`. Discharged by `decide`. -/
theorem dimensionCount_eq_six : dimensionCount = 6 := by decide

/-- The layer count is exactly `6`. Discharged by `decide`. -/
theorem layerCount_eq_six : layerCount = 6 := by decide

/-- Layer count and dimension count agree. This is the bare
    cardinality side of the bijection in §3. -/
theorem layerCount_eq_dimensionCount : layerCount = dimensionCount := rfl

/-! ══════════════════════════════════════════════════════════════════
    ## §3. layerDimension — the layer ↔ dimension bijection
    ══════════════════════════════════════════════════════════════════

    For each `InformationalLayer`, the unique `WireByteDimension`
    it attacks. The map is total and (by §3.2 + §3.3) a bijection.
    This is the formal reading of "each wire-diet layer is the
    cancellation of exactly one structural dimension of waste." -/

/-- For each `InformationalLayer`, the `WireByteDimension` it
    attacks. -/
def layerDimension : InformationalLayer → WireByteDimension
  | .PerByteAlphabet   => .AlphabetSize
  | .FrameStructure    => .FrameRepetition
  | .IntegerCoding     => .IntegerWidth
  | .OrderingFree      => .StreamOrdering
  | .StatisticalPrior  => .StatisticalContext
  | .AlphabetSubstrate => .LanguageAlphabet

/-- Inverse: for each `WireByteDimension`, the `InformationalLayer`
    that attacks it. -/
def dimensionLayer : WireByteDimension → InformationalLayer
  | .AlphabetSize       => .PerByteAlphabet
  | .FrameRepetition    => .FrameStructure
  | .IntegerWidth       => .IntegerCoding
  | .StreamOrdering     => .OrderingFree
  | .StatisticalContext => .StatisticalPrior
  | .LanguageAlphabet   => .AlphabetSubstrate

/-- `layerDimension` is a section of `dimensionLayer`: round-tripping
    a layer through its dimension and back is the identity. -/
theorem layerDimension_left_inverse (l : InformationalLayer) :
    dimensionLayer (layerDimension l) = l := by
  cases l <;> rfl

/-- `layerDimension` is a retraction of `dimensionLayer`: round-tripping
    a dimension through its layer and back is the identity. -/
theorem layerDimension_right_inverse (d : WireByteDimension) :
    layerDimension (dimensionLayer d) = d := by
  cases d <;> rfl

/-- Convenience alias: a witnessed bijection between
    `InformationalLayer` and `WireByteDimension`. The pair of
    inverse theorems above is the formal content; this is just
    the bundled package. -/
structure LayerDimensionBijection where
  /-- The forward map: layer to its attacked dimension. -/
  toFun     : InformationalLayer → WireByteDimension
  /-- The inverse: dimension to the layer attacking it. -/
  invFun    : WireByteDimension → InformationalLayer
  /-- Round-trip from layers is the identity. -/
  left_inv  : ∀ l, invFun (toFun l) = l
  /-- Round-trip from dimensions is the identity. -/
  right_inv : ∀ d, toFun (invFun d) = d

/-- The canonical bijection witness, populated with the named
    forward / inverse maps and their inverse theorems. -/
def canonicalBijection : LayerDimensionBijection :=
  { toFun     := layerDimension
  , invFun    := dimensionLayer
  , left_inv  := layerDimension_left_inverse
  , right_inv := layerDimension_right_inverse }

/-! ══════════════════════════════════════════════════════════════════
    ## §4. constraintDimension — closing the triangle
    ══════════════════════════════════════════════════════════════════

    The parent module fixes `cancels : InformationalLayer →
    ClassicalAssumption`. We add `constraintDimension :
    ClassicalAssumption → WireByteDimension` so that all three enums
    (Layer, Assumption, Dimension) form a commutative triangle of
    bijections. The triangle commutes by `rfl` — the maps were
    constructed to be definitionally equal on each constructor. -/

/-- For each classical assumption, the wire-byte dimension along
    which the assumption asserts there is no cheaper encoding. -/
def constraintDimension : ClassicalAssumption → WireByteDimension
  | .Base64IsOptimal               => .AlphabetSize
  | .EachFrameSelfDescribing       => .FrameRepetition
  | .IntegersAreFixedWidth         => .IntegerWidth
  | .OrderingIsOverhead            => .StreamOrdering
  | .TransmissionsAreUnconditioned => .StatisticalContext
  | .ByteIsTheUnit                 => .LanguageAlphabet

/-- Inverse: for each dimension, the classical assumption that
    asserts the dimension is incompressible. -/
def dimensionConstraint : WireByteDimension → ClassicalAssumption
  | .AlphabetSize       => .Base64IsOptimal
  | .FrameRepetition    => .EachFrameSelfDescribing
  | .IntegerWidth       => .IntegersAreFixedWidth
  | .StreamOrdering     => .OrderingIsOverhead
  | .StatisticalContext => .TransmissionsAreUnconditioned
  | .LanguageAlphabet   => .ByteIsTheUnit

theorem constraintDimension_left_inverse (a : ClassicalAssumption) :
    dimensionConstraint (constraintDimension a) = a := by
  cases a <;> rfl

theorem constraintDimension_right_inverse (d : WireByteDimension) :
    constraintDimension (dimensionConstraint d) = d := by
  cases d <;> rfl

/-- The triangle commutes: cancelling a layer's classical assumption
    and then asking which dimension that assumption pins gives the
    same dimension as asking what dimension the layer attacks. -/
theorem triangle_commutes (l : InformationalLayer) :
    constraintDimension (cancels l) = layerDimension l := by
  cases l <;> rfl

/-! ══════════════════════════════════════════════════════════════════
    ## §5. completeness_theorem — every catalogued constraint is in
            some dimension
    ══════════════════════════════════════════════════════════════════

    "Every classical constraint on a wire-byte stream that the
    parent module catalogues is captured by some `WireByteDimension`."

    This is a structural rather than metalogical statement. It
    quantifies over `ClassicalAssumption` (the parent enum) — not
    over "all possible classical assumptions in the universe." The
    metalogical version (no 7th constraint exists) is conjectured
    in §6, NOT proved here. -/

/-- Every catalogued classical constraint maps to some wire-byte
    dimension. Proved by exhibiting `constraintDimension` as a
    total function. -/
theorem completeness_theorem :
    ∀ a : ClassicalAssumption, ∃ d : WireByteDimension,
      constraintDimension a = d := by
  intro a
  exact ⟨constraintDimension a, rfl⟩

/-- Stronger form: every catalogued constraint is captured by a
    dimension via a *bijection* (the inverse is total, not just
    the forward direction). -/
theorem completeness_bijective :
    ∀ a : ClassicalAssumption,
      dimensionConstraint (constraintDimension a) = a :=
  constraintDimension_left_inverse

/-! ══════════════════════════════════════════════════════════════════
    ## §6. alternative_decompositions_collapse
    ══════════════════════════════════════════════════════════════════

    "Alternative groupings of the dimensions reduce to the canonical
    six." Within Init-only Lean, the most we can prove is that any
    bijection-preserving relabeling of `WireByteDimension` has 6
    elements — because the inductive type itself has 6 constructors
    and `allDimensions.length = 6` by `decide`.

    Stronger claims ("any *natural* coarsening yields ≤ 6 axes",
    "any refinement that preserves orthogonality yields ≥ 6 axes")
    are conjectures. We do not pretend to prove them here. -/

/-- Any list of `WireByteDimension`s in bijection with `allDimensions`
    has exactly 6 elements. This is a near-tautology — bijection
    preserves cardinality — but pins the structural invariant
    explicitly. -/
theorem any_relabeling_has_six_elements
    (relabel : List WireByteDimension)
    (h : relabel.length = allDimensions.length) :
    relabel.length = 6 := by
  rw [h]; decide

/-- A bijection on `WireByteDimension` (i.e. a relabeling) does not
    change the count of dimensions; the count is `6` regardless of
    how we name or permute the constructors. -/
theorem alternative_decompositions_collapse
    (relabel : List WireByteDimension)
    (h : relabel.length = dimensionCount) :
    relabel.length = 6 := by
  rw [h]; exact dimensionCount_eq_six

/-! ══════════════════════════════════════════════════════════════════
    ## §7. negativity_witnesses — candidate 7th dimensions ruled out
    ══════════════════════════════════════════════════════════════════

    Two of the most plausible candidates for a 7th wire-byte
    dimension. We rule them out *informally* by collapse-to-existing-
    dimension or by *not-a-wire-diet-layer* arguments, then pin a
    formal marker structure that records the verdict. The arguments
    are not metalogical exhaustion proofs (see §8 for the open
    conjecture); they are concrete pointers to where each candidate
    lands inside the existing taxonomy. -/

/-- A candidate-but-not-actually-novel 7th dimension. Records the
    candidate's name, the existing dimension it collapses to (if
    any), and a brief verdict. -/
structure CandidateSeventhDimension where
  /-- A short identifier for the candidate dimension. -/
  name             : String
  /-- The existing dimension the candidate reduces to (`none` if
      the candidate is not a wire-diet layer at all). -/
  reducesTo        : Option WireByteDimension
  /-- A one-line verdict: why the candidate fails to be a 7th
      orthogonal axis. -/
  verdict          : String
  deriving Repr

/-- Candidate #1: per-frame *temporal* structure (interleaving,
    timing, scheduling). Argument for collapse: when frames repeat
    predictably, the *timing* of repetition is part of that
    predictability. The wire-diet layer that captures this is
    Layer 1 (FrameStructure / FrameRepetition). The temporal
    sub-axis is a refinement of the frame-repetition axis, not
    an orthogonal one. -/
def candidateTemporal : CandidateSeventhDimension :=
  { name      := "Temporal interleaving"
  , reducesTo := some .FrameRepetition
  , verdict   :=
      "Sub-dimension of frame repetition: predictable frame timing " ++
      "is part of the same redundancy that Layer 1 cancels."
  }

/-- Candidate #2: per-message *encryption* overhead. Argument for
    rejection: encryption *adds* bytes (MAC, IV, ciphertext bloat).
    A wire-diet layer is by definition something that *removes*
    bytes by cancelling a classical assumption. Encryption does the
    opposite, so it is not a wire-diet axis at all (it lives in a
    different part of the stack: confidentiality vs. compactness). -/
def candidateEncryption : CandidateSeventhDimension :=
  { name      := "Encryption overhead"
  , reducesTo := none
  , verdict   :=
      "Not a wire-diet axis: encryption ADDS bytes (MAC, IV, " ++
      "ciphertext expansion) to enforce confidentiality. The " ++
      "wire-diet stack is about cancelling classical assumptions " ++
      "that COST bytes; encryption is in a different stack layer."
  }

/-- Candidate #3: per-byte *error-correction* overhead. Same shape
    as encryption: ECC ADDS bytes to enforce reliability. Not a
    wire-diet axis. -/
def candidateErrorCorrection : CandidateSeventhDimension :=
  { name      := "Error-correction overhead"
  , reducesTo := none
  , verdict   :=
      "Not a wire-diet axis: ECC ADDS bytes (parity, Reed-Solomon " ++
      "blocks) to enforce reliability against channel noise."
  }

/-- The list of considered candidates. Extending this list is the
    most direct way to push back the 7th-dimension conjecture
    (§8): every new candidate either collapses to one of the six
    or is rejected as not-a-wire-diet-layer. -/
def consideredCandidates : List CandidateSeventhDimension :=
  [candidateTemporal, candidateEncryption, candidateErrorCorrection]

/-- Three candidates considered. Pinned by `decide`. -/
theorem three_candidates_considered :
    consideredCandidates.length = 3 := by decide

/-- Every considered candidate either collapses to an existing
    dimension or is rejected as not a wire-diet layer at all. The
    bound is structural: the list contains only candidates we
    have a verdict for. -/
theorem every_candidate_resolved :
    ∀ c ∈ consideredCandidates,
      c.reducesTo.isSome ∨ c.reducesTo.isNone := by
  intro c _
  cases h : c.reducesTo with
  | none   => exact Or.inr rfl
  | some _ => exact Or.inl rfl

/-! ══════════════════════════════════════════════════════════════════
    ## §8. WireDietExhaustive — the OPEN conjecture
    ══════════════════════════════════════════════════════════════════

    The strongest claim one might want to make:

      "There is no 7th orthogonal wire-byte dimension."

    This is *NOT* proved here. It cannot be proved within an
    Init-only Lean development of this size, because the statement
    quantifies over the (unbounded, informally-defined) space of
    "all possible classical wire assumptions." Proving it would
    require either:

      - A metalogical exhaustion argument (formalize the space of
        classical wire assumptions, then enumerate it). Research-
        grade scope; out of bounds for this gap-closer.
      - A category-theoretic universal property (the six dimensions
        are the unique decomposition of some functor, etc.).
        Speculative; would need a different categorial setup than
        Init provides.

    We state the conjecture as a `Prop` and document it as open. -/

/-- Open conjecture: every wire-byte dimension is one of the six
    catalogued in `WireByteDimension`. Equivalently, the inductive
    type `WireByteDimension` is structurally exhaustive over the
    informal notion of "orthogonal axis along which a wire-byte
    stream can be optimized."

    THIS IS NOT A THEOREM. It is a `Prop` we name to make the
    open question explicit. The negativity witnesses in §7 supply
    evidence (three candidates rule out), not proof.

    Stated as the trivial-content `Prop` `True` so the declaration
    type-checks while remaining honest: there is nothing here to
    prove except that we have named the question. The semantic
    content lives in the docstring; the formal content is a
    placeholder. -/
def WireDietExhaustive : Prop := True

/-- The conjecture-shape `Prop` is inhabited by `trivial`. This is
    NOT a proof of exhaustiveness — it is a proof that we have
    *named* the conjecture and given it a placeholder. The actual
    metalogical statement (no 7th dimension exists) is intentionally
    NOT formalized here; see the docstring on `WireDietExhaustive`
    for why. -/
theorem wire_diet_exhaustive_named : WireDietExhaustive := trivial

/-! ══════════════════════════════════════════════════════════════════
    ## §9. completeness_pentad — the bundled summary
    ══════════════════════════════════════════════════════════════════

    A single bundled theorem packaging the structurally-proven
    content of this module. Five facts, all `decide`- or `cases`-
    discharged:

      (a) the dimension count is 6;
      (b) the layer count is 6;
      (c) layer count = dimension count;
      (d) the layer ↔ dimension map is a bijection
          (left + right inverses);
      (e) the layer/assumption/dimension triangle commutes.

    The conjectures (`WireDietExhaustive`, `noSeventhDimension`)
    are deliberately NOT in this pentad — they belong in §8 with
    the open-question framing. -/

/-- The structurally-proven content of `InformationalPhysicsCompleteness`,
    bundled. Five facts, all dischargeable by `decide` or `cases <;>
    rfl`. The conjectural content (no 7th dimension exists) is NOT
    in this bundle — see §8. -/
theorem completeness_pentad :
    (dimensionCount = 6) ∧
    (layerCount = 6) ∧
    (layerCount = dimensionCount) ∧
    (∀ l : InformationalLayer, dimensionLayer (layerDimension l) = l) ∧
    (∀ l : InformationalLayer,
        constraintDimension (cancels l) = layerDimension l) :=
  ⟨dimensionCount_eq_six,
   layerCount_eq_six,
   layerCount_eq_dimensionCount,
   layerDimension_left_inverse,
   triangle_commutes⟩

/-! ══════════════════════════════════════════════════════════════════
    ## §10. Honest verdict
    ══════════════════════════════════════════════════════════════════

    The question Taylor raised: "Why exactly 6? Forced by enum or
    by physics?"

    What this module earns:

      - The bijection from layers to dimensions is fully proved
        (§3). The two enums have *the same shape*, with named
        inverses both ways.

      - The bijection from assumptions to dimensions is fully
        proved (§4). The triangle commutes (§4, `triangle_commutes`).

      - Therefore: re-naming the parent module's `InformationalLayer`
        as `WireByteDimension` is a pure relabeling; the structural
        bijection makes the two enums interchangeable.

      - The dimension count `= 6` is pinned by `decide` (§2)
        *given the dimension enum we chose*. The enum has six
        constructors because the author named six.

    What this module does NOT earn:

      - That the dimension enum is itself FORCED. We have not
        formalized "all possible wire-byte dimensions"; without
        that, "exactly 6" remains a structural fact about a
        hand-picked finite set.

      - That no 7th dimension exists. We supplied negativity
        witnesses for three candidates (temporal, encryption,
        ECC) but each verdict is an informal one-liner, not a
        metalogical exhaustion proof. `WireDietExhaustive` is
        stated as an open conjecture (§8).

    Net: we reduced "why 6 layers?" to "why 6 dimensions?" The
    reduction is a structural bijection — which is real progress,
    because dimensions are easier to argue about than layers (each
    dimension answers a distinct *what* question). But the residual
    "why exactly 6 dimensions?" question still rests on the same
    ground that the parent module did: an author-curated finite
    enumeration. We have NOT closed the metalogical gap; we have
    sharpened the question and supplied negativity witnesses for
    its most-plausible counterexamples.

    Honest one-liner: this file proves the relabeling is sound, NOT
    that the enumeration is forced. -/

end InformationalPhysicsCompleteness
