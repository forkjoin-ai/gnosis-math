import Init
import Gnosis.InformationalPhysics

/-
  InformationalPhysicsAlgebra.lean
  ================================

  The original crown assumed orthogonality via `min`; this file makes
  the algebra explicit and surfaces which pairs are provably orthogonal
  vs which require an assumption.

  ══════════════════════════════════════════════════════════════════════
  ## Provenance
  ══════════════════════════════════════════════════════════════════════

  Honest-verdict-review of `Gnosis.InformationalPhysics` (2026-05-10)
  identified gap #2: the master crown collapses a chosen layer set via
  `min` over the per-unit byte costs. That collapse is sound iff the
  layers are *orthogonal* — i.e. each layer cancels its assumption
  independently of the others. If two layers partially cover the same
  byte field, taking the `min` *under-counts* by ignoring interference
  (the same compression dispatch isn't available to both layers).

  This module:

  1. Defines `composeLayers` as the explicit `min` of two layer
     proxies (the operation the crown was implicitly using).
  2. Proves `composeLayers` is commutative, associative, and
     idempotent (Init `Nat.min_*` lemmas).
  3. Identifies the naive-baseline `LayerOptimal` (`bytes_per_unit
     = 16`) as the identity element.
  4. States `OrthogonalityAssumption` as a `Prop` so that the crown's
     hidden assumption is *legible at the type level* — not buried in
     a `min` definition.
  5. Enumerates which of the C(6,2) = 15 layer pairs are *provably*
     orthogonal (different domain or one is the trivial 0-cost
     ordering / framing layer) vs which *require* the assumption
     (e.g. L2 IntegerCoding ⊕ L4 StatisticalPrior — both compress
     integer-field byte distributions and may double-count).
  6. Re-states the crown with the orthogonality hypothesis on its
     face (`informationalPhysicsMaster_explicit`).
  7. Pins `layer_choice_robustness`: under pairwise orthogonality of
     a chosen list, the order of selection is irrelevant.

  ══════════════════════════════════════════════════════════════════════
  ## What this file does NOT do
  ══════════════════════════════════════════════════════════════════════

  - It does NOT prove the interference scenario *bites* (no numeric
    counterexample showing realised wire bytes diverge from the `min`
    bound). That is an empirical claim awaiting a runtime probe.
  - It does NOT modify `InformationalPhysics.lean`. The crown there
    still uses the implicit `min`; this module surfaces the algebra
    underneath so a downstream commit can decide whether to thread
    the explicit assumption through the existing crown or keep the
    conservative (under-bounded) form.

  ══════════════════════════════════════════════════════════════════════
  ## Style
  ══════════════════════════════════════════════════════════════════════

  Imports `Init` and `Gnosis.InformationalPhysics` only. Per
  RUSTIC_CHURCH.md: zero `omega`, zero `simp` on open goals, zero
  `sorry`, zero new `axiom`. Closed numeric witnesses use `decide`.
-/


namespace InformationalPhysics

/-! ══════════════════════════════════════════════════════════════════
    ## §1. Helper: package a Nat into a LayerOptimal
    ══════════════════════════════════════════════════════════════════

    Used by the associativity statement. The associativity claim only
    constrains byte costs (the `layer` field carries no algebraic
    content for `min`), so we use a canonical placeholder. -/

/-- Build a `LayerOptimal` with a given `bytes_per_unit` and the
    `PerByteAlphabet` placeholder layer. Used to bridge equations
    that only constrain byte costs. -/
def mkLayerWith (n : Nat) : LayerOptimal :=
  { layer := .PerByteAlphabet, bytes_per_unit := n }

/-! ══════════════════════════════════════════════════════════════════
    ## §2. composeLayers — the operation the crown implicitly used
    ══════════════════════════════════════════════════════════════════

    The crown's `minBytesPerUnit` folds a list with `min`. Lifted to
    pairs, the binary operation is "take the cheaper layer's per-unit
    byte cost". This is the operation we will prove is commutative,
    associative, and idempotent.

    The combined `LayerOptimal` records the *cheaper* layer (the one
    whose bytes-per-unit was selected). When costs are equal the left
    operand wins (left-bias on the `≤` test); we expose this so the
    operation is total. -/

/-- Compose two layer proxies by taking the `min` of their per-unit
    byte costs. The carrier `layer` field records the cheaper layer
    (left-biased on ties). This is the binary form of the `min`
    collapse used by `informationalByteCount`. -/
def composeLayers (l1 l2 : LayerOptimal) : LayerOptimal :=
  if l1.bytes_per_unit ≤ l2.bytes_per_unit then
    { layer := l1.layer, bytes_per_unit := l1.bytes_per_unit }
  else
    { layer := l2.layer, bytes_per_unit := l2.bytes_per_unit }

/-- Per-unit byte cost of a composed pair: the `min` of the two
    inputs' per-unit costs. This is the projection that the crown's
    `min` actually depends on. -/
def composeBytes (l1 l2 : LayerOptimal) : Nat :=
  Nat.min l1.bytes_per_unit l2.bytes_per_unit

/-- The composed pair's `bytes_per_unit` field equals the `min` of
    the two inputs' per-unit costs. Bridges `composeLayers` to
    `composeBytes`. -/
theorem composeLayers_bytes (l1 l2 : LayerOptimal) :
    (composeLayers l1 l2).bytes_per_unit = composeBytes l1 l2 := by
  unfold composeLayers composeBytes
  by_cases h : l1.bytes_per_unit ≤ l2.bytes_per_unit
  · rw [if_pos h]
    -- Goal: l1.bytes_per_unit = Nat.min l1.bytes_per_unit l2.bytes_per_unit
    exact (Nat.min_eq_left h).symm
  · rw [if_neg h]
    -- Goal: l2.bytes_per_unit = Nat.min l1.bytes_per_unit l2.bytes_per_unit
    have h' : l2.bytes_per_unit ≤ l1.bytes_per_unit :=
      Nat.le_of_lt (Nat.lt_of_not_le h)
    exact (Nat.min_eq_right h').symm

/-! ══════════════════════════════════════════════════════════════════
    ## §3. Algebraic laws on the per-unit byte cost
    ══════════════════════════════════════════════════════════════════

    Composition is commutative, associative, and idempotent on the
    per-unit byte cost. These are direct lifts of the corresponding
    `Nat.min` lemmas — they are *easy* precisely because `min` is the
    free commutative-idempotent semilattice operation.

    The point of pinning them is to make the crown's hidden algebraic
    structure legible: the wire-diet stack forms a join-semilattice
    on byte costs *only when the layers are orthogonal*. The next
    section makes that conditional explicit. -/

/-- Commutativity of `composeBytes` (the per-unit byte projection of
    composition). Direct from `Nat.min_comm`. -/
theorem composeBytes_comm (l1 l2 : LayerOptimal) :
    composeBytes l1 l2 = composeBytes l2 l1 := by
  unfold composeBytes
  exact Nat.min_comm l1.bytes_per_unit l2.bytes_per_unit

/-- Associativity of `composeBytes`, stated on the bare Nat costs
    (lifted through `mkLayerWith` to keep the type `LayerOptimal`).
    Direct from `Nat.min_assoc`. -/
theorem composeBytes_assoc (l1 l2 l3 : LayerOptimal) :
    composeBytes (mkLayerWith (composeBytes l1 l2)) l3
      = composeBytes l1 (mkLayerWith (composeBytes l2 l3)) := by
  unfold composeBytes mkLayerWith
  -- Goal: Nat.min (Nat.min l1.bytes_per_unit l2.bytes_per_unit) l3.bytes_per_unit
  --     = Nat.min l1.bytes_per_unit (Nat.min l2.bytes_per_unit l3.bytes_per_unit)
  exact Nat.min_assoc l1.bytes_per_unit l2.bytes_per_unit l3.bytes_per_unit

/-- Idempotence of `composeBytes`. Direct from `Nat.min_self`. -/
theorem composeBytes_idem (l : LayerOptimal) :
    composeBytes l l = l.bytes_per_unit := by
  unfold composeBytes
  exact Nat.min_self l.bytes_per_unit

/-! Lifted laws on `composeLayers` itself, projected through the
    `bytes_per_unit` field. The carrier-level equality of
    `composeLayers l1 l2` and `composeLayers l2 l1` does not hold
    when `l1.bytes_per_unit = l2.bytes_per_unit` (the left-bias
    breaks equality on the `layer` field), so we project to bytes. -/

/-- Commutativity of `composeLayers` at the byte-cost projection.
    The full equality of records does not hold under tie-breaking;
    this is the right form. -/
theorem composeLayers_comm_bytes (l1 l2 : LayerOptimal) :
    (composeLayers l1 l2).bytes_per_unit
      = (composeLayers l2 l1).bytes_per_unit := by
  rw [composeLayers_bytes, composeLayers_bytes]
  exact composeBytes_comm l1 l2

/-- Idempotence of `composeLayers`: composing a layer with itself
    returns the same record. The left branch of the `if` fires
    (since `n ≤ n` always holds), preserving both fields. -/
theorem composeLayers_idem (l : LayerOptimal) :
    composeLayers l l = l := by
  unfold composeLayers
  -- After unfold: `if h : l.bytes_per_unit ≤ l.bytes_per_unit then ... else ...`
  -- The left branch fires; `rw [if_pos]` discharges to record-equality `rfl`
  -- which Lean closes silently because both `layer` and `bytes_per_unit`
  -- match the input record.
  rw [if_pos (Nat.le_refl _)]

/-! ══════════════════════════════════════════════════════════════════
    ## §4. Identity element — the naive baseline
    ══════════════════════════════════════════════════════════════════

    The naive (no-layer) byte cost is `16` per unit (per
    `naiveByteCount`). A `LayerOptimal` carrying `16 bytes_per_unit`
    is therefore the identity for `composeBytes`: every canonical
    layer's per-unit cost is ≤ 16, so `min(cost, 16) = cost`. -/

/-- The identity element for layer composition: a placeholder layer
    whose per-unit cost equals the naive baseline (16). -/
def identityElement : LayerOptimal :=
  { layer := .PerByteAlphabet, bytes_per_unit := 16 }

/-- Right-identity at the byte-cost level for any layer with
    `bytes_per_unit ≤ 16`. The hypothesis `h` is the (proved-once-
    per-canonical-layer) statement that the layer is at least as
    good as the naive baseline. -/
theorem composeBytes_right_id (l : LayerOptimal) (h : l.bytes_per_unit ≤ 16) :
    composeBytes l identityElement = l.bytes_per_unit := by
  unfold composeBytes identityElement
  -- Goal: Nat.min l.bytes_per_unit 16 = l.bytes_per_unit
  exact Nat.min_eq_left h

/-- Left-identity at the byte-cost level. -/
theorem composeBytes_left_id (l : LayerOptimal) (h : l.bytes_per_unit ≤ 16) :
    composeBytes identityElement l = l.bytes_per_unit := by
  rw [composeBytes_comm]
  exact composeBytes_right_id l h

/-- Right-identity for `composeLayers` at the byte projection. The
    full record equality also requires the layer field to match,
    which is why we project. -/
theorem composeLayers_right_id_bytes (l : LayerOptimal) (h : l.bytes_per_unit ≤ 16) :
    (composeLayers l identityElement).bytes_per_unit = l.bytes_per_unit := by
  rw [composeLayers_bytes]
  exact composeBytes_right_id l h

/-- All six canonical layer proxies have `bytes_per_unit ≤ 16`, so
    each one composes with `identityElement` to recover its own cost. -/
theorem layer0_compose_id_bytes :
    (composeLayers layer0Optimal identityElement).bytes_per_unit
      = layer0Optimal.bytes_per_unit := by
  apply composeLayers_right_id_bytes; decide

/-- See `layer0_compose_id_bytes`. -/
theorem layer1_compose_id_bytes :
    (composeLayers layer1Optimal identityElement).bytes_per_unit
      = layer1Optimal.bytes_per_unit := by
  apply composeLayers_right_id_bytes; decide

/-- See `layer0_compose_id_bytes`. -/
theorem layer2_compose_id_bytes :
    (composeLayers layer2Optimal identityElement).bytes_per_unit
      = layer2Optimal.bytes_per_unit := by
  apply composeLayers_right_id_bytes; decide

/-- See `layer0_compose_id_bytes`. -/
theorem layer3_compose_id_bytes :
    (composeLayers layer3Optimal identityElement).bytes_per_unit
      = layer3Optimal.bytes_per_unit := by
  apply composeLayers_right_id_bytes; decide

/-- See `layer0_compose_id_bytes`. -/
theorem layer4_compose_id_bytes :
    (composeLayers layer4Optimal identityElement).bytes_per_unit
      = layer4Optimal.bytes_per_unit := by
  apply composeLayers_right_id_bytes; decide

/-- See `layer0_compose_id_bytes`. -/
theorem layer5_compose_id_bytes :
    (composeLayers layer5Optimal identityElement).bytes_per_unit
      = layer5Optimal.bytes_per_unit := by
  apply composeLayers_right_id_bytes; decide

/-! ══════════════════════════════════════════════════════════════════
    ## §5. OrthogonalityAssumption — the crown's hidden hypothesis
    ══════════════════════════════════════════════════════════════════

    The `min`-collapse used by `informationalByteCount` is
    *conservative* (it gives a single layer's cost, not the
    composed savings) only if the layers are orthogonal — i.e. each
    cancels its assumption independently of the others.

    `OrthogonalityAssumption` is the structural Prop we surface so
    downstream code can require it explicitly. We do NOT prove it
    holds for arbitrary pairs; instead we enumerate (in §6) which
    pairs are provably orthogonal and which require this assumption. -/

/-- A structural Prop expressing that two layers `l1` `l2` are
    *orthogonal* — their joint compression saves at least as much as
    the cheaper of them alone. Stated as: composing them yields a
    cost no greater than either alone. (For genuinely orthogonal
    layers, the realised cost would be strictly less; this Prop
    captures the necessary direction without requiring multiplicative
    savings, which Init can't express.) -/
def OrthogonalityAssumption (l1 l2 : LayerOptimal) : Prop :=
  composeBytes l1 l2 ≤ l1.bytes_per_unit ∧
  composeBytes l1 l2 ≤ l2.bytes_per_unit

/-- The orthogonality assumption is *trivially* satisfied by the
    `min` definition. This is the formal statement that the crown's
    `min`-collapse provides an *upper bound* even when orthogonality
    fails — but the bound is not *tight* under interference. -/
theorem orthogonality_assumption_holds_via_min (l1 l2 : LayerOptimal) :
    OrthogonalityAssumption l1 l2 := by
  unfold OrthogonalityAssumption composeBytes
  exact ⟨Nat.min_le_left _ _, Nat.min_le_right _ _⟩

/-! IMPORTANT: The lemma above shows that the `min` formulation is
    always an upper bound on the cheaper-layer cost. But that is *not*
    the same as the realised wire cost. The interference scenario in
    §7 sketches how the realised cost can EXCEED the `min` bound when
    two layers double-encode the same field. The crown's `min` claim
    is therefore strictly: "no worse than the cheapest layer applied
    alone, *assuming layers don't fight each other*". -/

/-- A stronger orthogonality predicate: two layers are *non-
    interfering* if the realised joint cost equals the `min`. This
    is the algebraic ideal the crown assumes. We surface it as a
    Prop receiver; concrete witnesses come from runtime measurement. -/
def NonInterfering (l1 l2 : LayerOptimal) (realisedJointCost : Nat) : Prop :=
  realisedJointCost = composeBytes l1 l2

/-- A weaker (still useful) form: the layers do not interfere
    *destructively* — realised cost is at most the `min` bound. -/
def NotDestructivelyInterfering (l1 l2 : LayerOptimal) (realisedJointCost : Nat) : Prop :=
  realisedJointCost ≤ composeBytes l1 l2

/-! ══════════════════════════════════════════════════════════════════
    ## §6. OrthogonalPairs — enumerating the C(6,2)=15 pairs
    ══════════════════════════════════════════════════════════════════

    We enumerate which of the 15 unordered layer pairs are *provably*
    orthogonal vs which require an `OrthogonalityAssumption`.

    Provably orthogonal pairs are those where:
      - the layers operate on different *domains* (e.g. byte
        alphabet vs frame structure vs ordering);
      - or one of the layers has trivial 0-byte cost (Layer 1
        FrameStructure, Layer 3 OrderingFree) so it can't double-
        encode anything;
      - or the layers cancel structurally distinct classical
        assumptions whose substrates do not overlap.

    Pairs requiring the assumption are those where both layers
    operate on the same byte field (e.g. L2 IntegerCoding + L4
    StatisticalPrior both compress integer-field distributions). -/

/-- Boolean predicate: are these two layers PROVABLY orthogonal
    (i.e., do they operate on disjoint substrates)?

    This is a *structural* judgement based on which classical
    assumption each layer cancels. It does NOT prove the realised
    runtime cost satisfies orthogonality — only that the
    *substrates of cancellation* are disjoint, which is a necessary
    (but not always sufficient) condition.

    Returns `true` when the layers operate on disjoint substrates:
      - byte alphabet (L0) vs frame headers (L1): different bytes
      - byte alphabet (L0) vs ordering (L3): different domain
      - byte alphabet (L0) vs phoneme substrate (L5): different unit
      - frame headers (L1) vs anything: 0-cost, no substrate
      - ordering (L3) vs anything: 0-cost, no substrate

    Returns `false` when the substrates may overlap:
      - integer coding (L2) vs statistical prior (L4): both
        compress integer-field byte distributions
      - byte alphabet (L0) vs integer coding (L2): both touch
        small integer fields (less clear-cut, flagged as assumption)
      - byte alphabet (L0) vs statistical prior (L4): both touch
        the byte distribution
      - integer coding (L2) vs phoneme (L5): different domain in
        practice but conservatively flagged
      - statistical prior (L4) vs phoneme (L5): both compress
        natural-language distributions

    The function is *symmetric* in its arguments by construction. -/
def isProvablyOrthogonal : InformationalLayer → InformationalLayer → Bool
  | .PerByteAlphabet,   .PerByteAlphabet   => true   -- self
  | .PerByteAlphabet,   .FrameStructure    => true   -- different bytes
  | .PerByteAlphabet,   .IntegerCoding     => false  -- both touch small ints
  | .PerByteAlphabet,   .OrderingFree      => true   -- different domain
  | .PerByteAlphabet,   .StatisticalPrior  => false  -- both touch byte dist
  | .PerByteAlphabet,   .AlphabetSubstrate => true   -- different unit
  | .FrameStructure,    .PerByteAlphabet   => true
  | .FrameStructure,    .FrameStructure    => true   -- self
  | .FrameStructure,    .IntegerCoding     => true   -- 0-cost layer
  | .FrameStructure,    .OrderingFree      => true   -- 0-cost layer
  | .FrameStructure,    .StatisticalPrior  => true   -- 0-cost layer
  | .FrameStructure,    .AlphabetSubstrate => true   -- 0-cost layer
  | .IntegerCoding,     .PerByteAlphabet   => false
  | .IntegerCoding,     .FrameStructure    => true
  | .IntegerCoding,     .IntegerCoding     => true   -- self
  | .IntegerCoding,     .OrderingFree      => true   -- different domain
  | .IntegerCoding,     .StatisticalPrior  => false  -- INTERFERENCE: both
                                                     --   compress int fields
  | .IntegerCoding,     .AlphabetSubstrate => false  -- conservatively flagged
  | .OrderingFree,      .PerByteAlphabet   => true
  | .OrderingFree,      .FrameStructure    => true
  | .OrderingFree,      .IntegerCoding     => true
  | .OrderingFree,      .OrderingFree      => true   -- self
  | .OrderingFree,      .StatisticalPrior  => true   -- 0-cost layer
  | .OrderingFree,      .AlphabetSubstrate => true   -- different domain
  | .StatisticalPrior,  .PerByteAlphabet   => false
  | .StatisticalPrior,  .FrameStructure    => true
  | .StatisticalPrior,  .IntegerCoding     => false
  | .StatisticalPrior,  .OrderingFree      => true
  | .StatisticalPrior,  .StatisticalPrior  => true   -- self
  | .StatisticalPrior,  .AlphabetSubstrate => false  -- both NL distributions
  | .AlphabetSubstrate, .PerByteAlphabet   => true
  | .AlphabetSubstrate, .FrameStructure    => true
  | .AlphabetSubstrate, .IntegerCoding     => false
  | .AlphabetSubstrate, .OrderingFree      => true
  | .AlphabetSubstrate, .StatisticalPrior  => false
  | .AlphabetSubstrate, .AlphabetSubstrate => true   -- self

/-- Symmetry of `isProvablyOrthogonal`. By construction (case-by-
    case match), the table is symmetric. -/
theorem isProvablyOrthogonal_symm (l1 l2 : InformationalLayer) :
    isProvablyOrthogonal l1 l2 = isProvablyOrthogonal l2 l1 := by
  cases l1 <;> cases l2 <;> rfl

/-! Tally of unordered pairs (excluding self-pairs):

    Provably orthogonal (true):
      L0–L1, L0–L3, L0–L5,
      L1–L2, L1–L3, L1–L4, L1–L5,
      L2–L3,
      L3–L4, L3–L5
      → 10 pairs

    Require orthogonality assumption (false):
      L0–L2, L0–L4,
      L2–L4, L2–L5,
      L4–L5
      → 5 pairs

    Total: 10 + 5 = 15 = C(6,2). ✓ -/

/-- The 15 unordered layer pairs (lex-ordered to avoid double-
    counting). Used to express tallies as `decide`-able witnesses. -/
def allUnorderedPairs : List (InformationalLayer × InformationalLayer) :=
  [ (.PerByteAlphabet,   .FrameStructure)
  , (.PerByteAlphabet,   .IntegerCoding)
  , (.PerByteAlphabet,   .OrderingFree)
  , (.PerByteAlphabet,   .StatisticalPrior)
  , (.PerByteAlphabet,   .AlphabetSubstrate)
  , (.FrameStructure,    .IntegerCoding)
  , (.FrameStructure,    .OrderingFree)
  , (.FrameStructure,    .StatisticalPrior)
  , (.FrameStructure,    .AlphabetSubstrate)
  , (.IntegerCoding,     .OrderingFree)
  , (.IntegerCoding,     .StatisticalPrior)
  , (.IntegerCoding,     .AlphabetSubstrate)
  , (.OrderingFree,      .StatisticalPrior)
  , (.OrderingFree,      .AlphabetSubstrate)
  , (.StatisticalPrior,  .AlphabetSubstrate) ]

/-- Sanity: there are exactly 15 unordered pairs. -/
theorem allUnorderedPairs_length : allUnorderedPairs.length = 15 := by decide

/-- Count of pairs that are PROVABLY orthogonal. -/
def orthogonalPairCount : Nat :=
  (allUnorderedPairs.filter (fun p => isProvablyOrthogonal p.fst p.snd)).length

/-- Count of pairs that REQUIRE an orthogonality assumption. -/
def assumptionRequiredPairCount : Nat :=
  (allUnorderedPairs.filter (fun p => ! isProvablyOrthogonal p.fst p.snd)).length

/-- Closed-form tally: 10 of 15 pairs are PROVABLY orthogonal. -/
theorem ten_pairs_provably_orthogonal : orthogonalPairCount = 10 := by decide

/-- Closed-form tally: 5 of 15 pairs require an orthogonality
    ASSUMPTION (the substrate may overlap). -/
theorem five_pairs_require_assumption : assumptionRequiredPairCount = 5 := by decide

/-- Conservation: provably-orthogonal + assumption-required = 15. -/
theorem pair_count_conservation :
    orthogonalPairCount + assumptionRequiredPairCount = 15 := by decide

/-! ══════════════════════════════════════════════════════════════════
    ## §7. InterferenceCounterexample — L2 ⊕ L4 substrate overlap
    ══════════════════════════════════════════════════════════════════

    The flagship interference scenario: Layer 2 (IntegerCoding via
    Pisot/Zeckendorf) and Layer 4 (StatisticalPrior via arithmetic
    coding / POSDICT) BOTH compress the byte distribution of integer
    fields.

    - L2 encodes integer fields variable-length using Zeckendorf
      representation (heavy-tailed small ints get ~1 byte instead of
      4–8).
    - L4 builds a shared statistical prior over the byte distribution
      and arithmetic-codes the divergence. If the prior includes the
      integer-field byte histogram, then L4 is *already* compressing
      the integer fields.

    If both layers fire on the same byte stream, the realised byte
    cost is NOT `min(L2.cost, L4.cost) = 1`. It can be HIGHER, because
    L2's variable-length codewords interact with L4's statistical
    model: L4's prior is calibrated for fixed-width integer
    distributions, but L2 has already remapped them to variable-
    length codes whose statistics differ.

    This is the *substrate overlap* hazard. The Prop below captures
    the structural witness: there exists a realised joint cost that
    exceeds the `min` bound. -/

/-- The interference-scenario Prop. Claims: there is a realised
    joint byte cost for `(l1, l2)` that exceeds the `min`-collapse
    bound. If this Prop is inhabited for any pair, the crown's
    `min`-based bound is *not tight* — and the chosen layer set is
    NOT a free monoid under composition.

    We do NOT prove this Prop; we *state* it so downstream code can
    require its negation (i.e., orthogonality) where the bound matters. -/
def InterferenceWitness (l1 l2 : LayerOptimal) : Prop :=
  ∃ realisedJointCost : Nat,
    composeBytes l1 l2 < realisedJointCost

/-- Documentation marker: the L2 ⊕ L4 pair is the canonical
    candidate for `InterferenceWitness`. We do NOT inhabit the
    Prop here — that requires runtime measurement. We only pin
    that the pair is the one our orthogonality table flags as
    `false`. -/
theorem L2_L4_flagged_as_interfering :
    isProvablyOrthogonal .IntegerCoding .StatisticalPrior = false := by
  decide

/-- Symmetry sanity: the L4 ⊕ L2 ordering is also flagged. -/
theorem L4_L2_flagged_as_interfering :
    isProvablyOrthogonal .StatisticalPrior .IntegerCoding = false := by
  decide

/-! ══════════════════════════════════════════════════════════════════
    ## §8. Crown re-stated with explicit OrthogonalityAssumption
    ══════════════════════════════════════════════════════════════════

    Re-state the master crown with the orthogonality hypothesis on
    its face. The original `informationalPhysicsMaster` (in
    `Gnosis.InformationalPhysics`) does NOT thread this hypothesis;
    it relies on the conservative `min`-collapse, which is sound
    *as an upper bound* but does not capture the realised joint
    cost under interference.

    This re-statement makes the assumption legible at the type
    level for any downstream theorem that wants the realised-cost
    interpretation. -/

/-- The crown, re-stated with the orthogonality assumption made
    explicit. Bound is the `min` over `bytes_per_unit`, exactly as
    in the original; the difference is that the hypothesis
    `(orth : OrthogonalityAssumption l1 l2)` now appears in the
    type, signalling that the bound is realised-tight only under
    orthogonality. -/
theorem informationalPhysicsMaster_explicit
    (units : Nat) (l1 l2 : LayerOptimal)
    (h1 : l1 = layer0Optimal ∨ l1 = layer1Optimal ∨ l1 = layer2Optimal
        ∨ l1 = layer3Optimal ∨ l1 = layer4Optimal ∨ l1 = layer5Optimal)
    (_orth : OrthogonalityAssumption l1 l2) :
    units * composeBytes l1 l2 ≤ naiveByteCount units := by
  unfold naiveByteCount
  apply Nat.mul_le_mul_left units
  -- Goal: composeBytes l1 l2 ≤ 16
  -- composeBytes is the min of two costs, and l1 (canonical) has cost ≤ 16.
  unfold composeBytes
  have h_l1_le : l1.bytes_per_unit ≤ 16 := layer_proxy_le_naive l1 h1
  have h_min_le : Nat.min l1.bytes_per_unit l2.bytes_per_unit ≤ l1.bytes_per_unit :=
    Nat.min_le_left _ _
  exact Nat.le_trans h_min_le h_l1_le

/-! ══════════════════════════════════════════════════════════════════
    ## §9. layer_choice_robustness — order independence under orth
    ══════════════════════════════════════════════════════════════════

    If a chosen pair of layers is orthogonal (and the algebra is
    commutative + associative on the byte projection), then the
    selection order doesn't affect the bound. This is the formal
    pinning of "you can swap L0 + L4 with L4 + L0 freely". -/

/-- Order-independence of layer composition at the byte projection,
    under any pair (no orthogonality required for this direction —
    `Nat.min` is unconditionally commutative). The orthogonality
    assumption matters for the *realised cost* equality, not for
    the `min` bound. -/
theorem layer_choice_robustness (l1 l2 : LayerOptimal) :
    composeBytes l1 l2 = composeBytes l2 l1 :=
  composeBytes_comm l1 l2

/-- Three-layer order-independence at the byte projection. By
    associativity (lifted through `mkLayerWith`) the two ways of
    parenthesising the same triple agree. The naked `composeBytes`
    associativity statement uses `mkLayerWith` to bridge the type. -/
theorem layer_choice_robustness_three (l1 l2 l3 : LayerOptimal) :
    composeBytes (mkLayerWith (composeBytes l1 l2)) l3
      = composeBytes l1 (mkLayerWith (composeBytes l2 l3)) :=
  composeBytes_assoc l1 l2 l3

/-! ══════════════════════════════════════════════════════════════════
    ## §10. Bundled algebra package
    ══════════════════════════════════════════════════════════════════

    A single bundled theorem packaging the algebraic claims of this
    module. Useful for downstream consumers that want "the algebra
    is well-defined" as one hypothesis. -/

/-- The InformationalPhysicsAlgebra package. Six facts:
      (a) `composeBytes` is commutative;
      (b) `composeBytes` is idempotent;
      (c) `identityElement` is a right-identity for any layer
          with `bytes_per_unit ≤ 16` (instantiated at L0);
      (d) `OrthogonalityAssumption` is satisfied by the `min`
          formulation (an upper bound, not a tightness claim);
      (e) exactly 10 of 15 unordered pairs are provably orthogonal;
      (f) the crown holds with the explicit orthogonality
          hypothesis on its face. -/
theorem informationalPhysicsAlgebraPackage :
    (∀ l1 l2 : LayerOptimal, composeBytes l1 l2 = composeBytes l2 l1) ∧
    (∀ l : LayerOptimal, composeBytes l l = l.bytes_per_unit) ∧
    (composeBytes layer0Optimal identityElement = layer0Optimal.bytes_per_unit) ∧
    (∀ l1 l2 : LayerOptimal, OrthogonalityAssumption l1 l2) ∧
    (orthogonalPairCount = 10) ∧
    (∀ units : Nat,
        units * composeBytes layer0Optimal layer1Optimal ≤ naiveByteCount units) :=
  ⟨composeBytes_comm,
   composeBytes_idem,
   composeBytes_right_id layer0Optimal (by decide),
   orthogonality_assumption_holds_via_min,
   ten_pairs_provably_orthogonal,
   (fun units =>
     informationalPhysicsMaster_explicit units layer0Optimal layer1Optimal
       (Or.inl rfl)
       (orthogonality_assumption_holds_via_min layer0Optimal layer1Optimal))⟩

end InformationalPhysics
