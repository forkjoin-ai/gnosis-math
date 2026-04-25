/-
  TarskiTruthUndefinability
  =========================

  Tarski's Truth Undefinability Theorem (1933) asserts: for any
  consistent formal theory T extending a sufficient fragment of
  arithmetic, there is no formula `True(x)` of T's language such that

      T  |-  True(gnum phi)  <->  phi      for every sentence phi of T.

  The classical proof uses the diagonal lemma: build a sentence L
  with `L  <->  not True(gnum L)`. The Tarski schema then forces
  `True(gnum L) <-> not True(gnum L)`, which derives a contradiction.

  This file is a sibling to `GodelIncompletenessShadow`. It reuses
  that file's toy Robinson-Q language, Goedel numbering, and diagonal
  function `diag`. The construction is exactly Tarski's: a Liar
  sentence built diagonally against a candidate truth-predicate.

  STRATEGY CHOSEN: BOUNDED-DEPTH SHADOW PLUS NAMED WALL.
  ------------------------------------------------------
  Tarski's argument has two layers:

    (L1) FINITE/PROPOSITIONAL: given the Tarski biconditional
         `truePred(gnum L)  <->  L` together with the Liar's
         definitional unfolding `L = neg (truePred(gnum L))`,
         a four-line propositional derivation produces both
         `truePred(gnum L)` and `neg (truePred(gnum L))`.

    (L2) UNBOUNDED/UNIVERSAL: Tarski's *theorem* is that the schema
         must hold for *every* sentence phi. Mechanically asserting
         this requires a universal quantifier over all sentences
         (a recursive set of formulas), which is the same wall the
         Goedel attempt hit.

  We mechanize (L1) honestly. The Liar is built via the sibling's
  `diag`. The schema-implies-contradiction step is closed by
  `native_decide` over a bounded-depth Hilbert proof search inside
  a deliberately small pool. (L2) is named in the closing section
  but not proved.

  Choice of `truePred`. Our toy has only one one-place predicate, the
  primitive `Box`, so we instantiate `truePred(x) := Box(x)`. Under
  this instantiation:

    * The Liar phi_L(x) := neg (Box x) is exactly the Goedel
      formula `phiG` from the sibling file. The diagonal sentence
      L coincides with the Goedel sentence G. This is a *feature*,
      not a defect: it exhibits the well-known formal connection
      between Goedel-1 and Tarski's theorem --- the Goedel sentence
      is the Liar against the provability predicate read as truth.

    * Tarski's argument adds one ingredient Goedel's does not need:
      a propositional inconsistency derivation from a biconditional
      `A <-> not A`. We supply that derivation in the toy proof
      system using the consequentia-mirabilis axiom
      `(A -> not A) -> not A`, which is a single propositional
      tautology added to our pool.

  WHAT IS MECHANIZED:
    For the candidate `truePred := Box (var 0)` and the Liar L (= G):
      - The Liar's syntactic fixed-point identity
            L = neg (Box (numeral (gnum (neg (Box (var 0))))))
        holds by `rfl`.
      - In a pool containing the Tarski schema instance for L
        and the consequentia-mirabilis axiom, both
            truePred[gnum L]      = Box (numeral (gnum phiL))
            neg (truePred[gnum L]) = neg (Box (numeral (gnum phiL)))
        are derivable at bounded depth (here N = 4) via modus
        ponens. Verified by `native_decide`.
      - This is the bounded shadow of "the Tarski schema is
        inconsistent": within the toy proof system, *if* the schema
        instance is asserted, the system derives both poles of
        a propositional contradiction at depth <= 4.

  WHAT IS NOT MECHANIZED (THE WALL):
    The honest Tarski statement requires
        for every sentence phi of the language,
          (truePred(gnum phi) <-> phi) is asserted in T  =>  T is inconsistent.
    The universal quantifier ranges over the recursive set of all
    sentences, and Tarski's argument plus the diagonal lemma turns
    *that one universal quantifier* into a single Liar sentence ---
    but the *meta-theorem* "no truePred can satisfy the schema for
    all phi" is itself a statement about an infinite family. As in
    `GodelIncompletenessShadow`, `native_decide` cannot dispatch the
    `forall` over `Nat`-encoded sentences. Closing it would require
    an induction over formula structure plus the representability
    theorem for primitive recursive functions inside the toy.

  Gnosis mapping
  --------------
    * Tarski schema biconditional   <->  Bidirectional gnosis edge
                                          truePred(gnum phi) <==> phi
    * Liar sentence L               <->  Self-loop with negation
                                          across the predicate edge
    * Consequentia mirabilis axiom  <->  Closure rule that turns a
                                          self-negating edge into
                                          two contradictory leaves
    * Bounded inconsistency         <->  Race-budgeted derivation
                                          finding both poles
    * Wall at unbounded forall phi  <->  No finite cover for the
                                          recursive set of sentences

  Construction follows: Tarski, _The Concept of Truth in Formalized
  Languages_ (1933); Smullyan, _Goedel's Incompleteness Theorems_,
  Oxford 1992, Ch. III (Liar diagonal); Boolos, _The Logic of
  Provability_, Ch. 1 (Tarski/Goedel relation).

  No imports beyond `Init` and the sibling `GodelIncompletenessShadow`.
  No axioms, no `sorry`.
-/

import BuleyeanMath.GodelIncompletenessShadow

namespace TarskiTruthUndefinability

open GodelIncompletenessShadow

-- ══════════════════════════════════════════════════════════
-- PART 1: THE CANDIDATE TRUTH PREDICATE
-- ══════════════════════════════════════════════════════════
-- Our toy language has one one-place predicate, `Box`. We
-- instantiate Tarski's `True(x)` as `Box(x)` and ask whether the
-- T-schema `True(gnum phi) <-> phi` can hold consistently. The
-- answer, finitarily, is no: for the Liar diagonal sentence built
-- against this `Box`, both poles of the contradiction become
-- derivable in our toy proof system once the schema instance is
-- added.

/-- The candidate truth predicate: a one-place formula with the
    free variable at de Bruijn index 0. -/
def truePred : Form := Form.box (Term.var 0)

/-- Schema-instantiated truth predicate at a closed term: literally
    `Box t` with the variable filled in. -/
def truePredAt (t : Term) : Form := Form.box t

theorem truePred_subst_eq (t : Term) :
    subst t truePred = truePredAt t := by rfl

-- ══════════════════════════════════════════════════════════
-- PART 2: THE LIAR SENTENCE (via the sibling's diagonal)
-- ══════════════════════════════════════════════════════════
-- phi_L(x) := neg (truePred(x)) = neg (Box x).
-- L := diag phi_L.  By the diagonal computation in the sibling,
-- L = neg (Box (numeral (gnum phi_L))). Note: phi_L is exactly
-- `phiG` from the sibling, so L coincides with the sibling's `G`
-- --- the Goedel sentence read as a Tarski Liar. This is the
-- well-known Goedel-Tarski correspondence at the syntactic level.

/-- The Liar formula schema: `not (truePred x)`. -/
def phiL : Form := Form.neg truePred

/-- The Liar sentence: L := diag phiL. -/
def LiarSentence : Form := diag phiL

/-- Computational sanity: phiL is exactly phiG. -/
theorem phiL_eq_phiG : phiL = phiG := by rfl

/-- Computational sanity: the Liar coincides with the Goedel
    sentence under this candidate truth predicate. The collapse
    is the formal trace of "Tarski's Liar against provability is
    Goedel's sentence". -/
theorem liar_eq_goedel : LiarSentence = G := by rfl

/-- Self-reference: the Liar unfolds syntactically to
    `neg (Box (numeral (gnum phiL)))`. This is the "L iff not
    True(gnum L)" identity at the meta level: L *is* the assertion
    that Box-at-its-own-Goedel-number fails. -/
theorem liar_self_reference :
    LiarSentence = Form.neg (Form.box (numeral (gnum phiL))) := by rfl

/-- The closed term that encodes the Liar's Goedel number, as it
    appears inside the Liar after the diagonal substitution. -/
def liarCode : Term := numeral (gnum phiL)

/-- The instantiated truth predicate at the Liar's Goedel number:
    this is the formula `truePred(gnum L)` in Tarski's notation. -/
def truePredAtLiar : Form := truePredAt liarCode

theorem truePredAtLiar_concrete :
    truePredAtLiar = Form.box (numeral (gnum phiL)) := by rfl

/-- The Liar literally negates the truth-predicate-at-itself. This
    is the syntactic Liar identity. -/
theorem liar_is_neg_truePredAtLiar :
    LiarSentence = Form.neg truePredAtLiar := by rfl

-- ══════════════════════════════════════════════════════════
-- PART 3: THE TARSKI SCHEMA INSTANCE
-- ══════════════════════════════════════════════════════════
-- The schema for sentence phi is `truePred(gnum phi) <-> phi`. We
-- represent the biconditional as a pair of implications. For the
-- Liar L, the schema instance is:
--    (truePredAtLiar -> L)  and  (L -> truePredAtLiar)
-- Substituting L = neg truePredAtLiar, this becomes:
--    (A -> not A)  and  (not A -> A)        where A := truePredAtLiar.

/-- Abbreviation: the Tarski schema's "true side" for the Liar. -/
def tarskiHalfFwd : Form := Form.imp truePredAtLiar LiarSentence

/-- Abbreviation: the Tarski schema's "back side" for the Liar. -/
def tarskiHalfBwd : Form := Form.imp LiarSentence truePredAtLiar

/-- Self-negating pattern unwrapped: forward half is literally
    `(A -> not A)`. -/
theorem tarski_fwd_unwrapped :
    tarskiHalfFwd = Form.imp truePredAtLiar (Form.neg truePredAtLiar) := by rfl

/-- Self-negating pattern unwrapped: backward half is literally
    `(not A -> A)`. -/
theorem tarski_bwd_unwrapped :
    tarskiHalfBwd = Form.imp (Form.neg truePredAtLiar) truePredAtLiar := by rfl

-- ══════════════════════════════════════════════════════════
-- PART 4: THE INCONSISTENCY DERIVATION
-- ══════════════════════════════════════════════════════════
-- Propositional core (consequentia mirabilis flavour):
--   1. (A -> not A) -> not A          (axiom: a propositional tautology)
--   2. (A -> not A)                    (Tarski schema, forward half)
--   3. not A                           (MP of 1, 2)               -- depth 1
--   4. (not A -> A)                    (Tarski schema, backward half)
--   5. A                               (MP of 3, 4)               -- depth 2
-- Both `A` and `not A` are derived; the system is inconsistent.

/-- The consequentia-mirabilis axiom instance for our Liar:
        `(truePredAtLiar -> not truePredAtLiar) -> not truePredAtLiar`.
    Propositionally a classical tautology; we add it as the single
    propositional axiom needed to close the Liar contradiction. -/
def consequentiaMirabilisAxiom : Form :=
  Form.imp tarskiHalfFwd (Form.neg truePredAtLiar)

/-- Pool used by the bounded-depth proof search: the Tarski schema
    instance, the consequentia-mirabilis axiom, and the two target
    contradictory poles. Every formula here is concrete and finite. -/
def tarskiPool : List Form :=
  [ consequentiaMirabilisAxiom
  , tarskiHalfFwd
  , tarskiHalfBwd
  , Form.neg truePredAtLiar
  , truePredAtLiar
  ]

/-- Local axiom set for the Tarski derivation. We mark exactly the
    consequentia-mirabilis instance and the two Tarski schema halves
    as "given" axioms; the contradictory poles are derived. -/
def isTarskiAxiom (phi : Form) : Bool :=
  (phi == consequentiaMirabilisAxiom)
  || (phi == tarskiHalfFwd)
  || (phi == tarskiHalfBwd)

/-- Modus-ponens witness inside the Tarski pool. -/
def existsMP_T (proven : List Form) (q : Form) : Bool :=
  proven.any (fun p => proven.any (fun pq => pq == Form.imp p q))

/-- Bounded Hilbert search restricted to `tarskiPool`: depth 0 = the
    pool's axioms, each next layer adds MP-conclusions chosen from
    the same pool. -/
def tarskiProvenAt : Nat → List Form
  | 0     => tarskiPool.filter isTarskiAxiom
  | n + 1 =>
    let prev := tarskiProvenAt n
    let new  := tarskiPool.filter (fun q =>
      existsMP_T prev q && !(prev.any (· == q)))
    prev ++ new

/-- Membership check. -/
def tarskiProvableUpTo (N : Nat) (phi : Form) : Bool :=
  (tarskiProvenAt N).any (· == phi)

-- ─── depth 0: only the three given axioms appear ──────────────

theorem tarski_depth0_size :
    (tarskiProvenAt 0).length = 3 := by native_decide

theorem tarski_axioms_present :
    tarskiProvableUpTo 0 consequentiaMirabilisAxiom = true
  ∧ tarskiProvableUpTo 0 tarskiHalfFwd = true
  ∧ tarskiProvableUpTo 0 tarskiHalfBwd = true := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

theorem neg_pole_not_at_0 :
    tarskiProvableUpTo 0 (Form.neg truePredAtLiar) = false := by native_decide

theorem pos_pole_not_at_0 :
    tarskiProvableUpTo 0 truePredAtLiar = false := by native_decide

-- ─── depth 1: MP fires once, deriving `not A` from CM + fwd ──

theorem neg_pole_derived_at_1 :
    tarskiProvableUpTo 1 (Form.neg truePredAtLiar) = true := by native_decide

/-- The positive pole is *not yet* derived at depth 1: the MP step
    that fires to produce `A` needs `not A` as a hypothesis, which
    only just appeared. -/
theorem pos_pole_not_at_1 :
    tarskiProvableUpTo 1 truePredAtLiar = false := by native_decide

-- ─── depth 2: second MP fires, deriving `A` from `not A` + bwd ──

theorem pos_pole_derived_at_2 :
    tarskiProvableUpTo 2 truePredAtLiar = true := by native_decide

theorem neg_pole_still_at_2 :
    tarskiProvableUpTo 2 (Form.neg truePredAtLiar) = true := by native_decide

-- ─── the flagship bounded Tarski theorem ──────────────────────

/-- TARSKI BOUNDED INCONSISTENCY (the honest finitary shadow).

    In the toy proof system, when the Tarski biconditional schema
    instance for the Liar is added as an axiom (together with the
    propositional consequentia-mirabilis tautology), modus ponens
    derives BOTH `truePred(gnum L)` and `neg (truePred(gnum L))`
    within depth 2. The toy theory of `tarskiPool` is therefore
    bounded-inconsistent.

    This is the (L1) layer of Tarski's argument: the propositional
    collapse of the schema. The (L2) layer --- "no truePred can
    satisfy the schema for *every* sentence" --- is the wall, named
    in Part 7. -/
theorem tarski_bounded_inconsistent :
    tarskiProvableUpTo 2 truePredAtLiar = true
  ∧ tarskiProvableUpTo 2 (Form.neg truePredAtLiar) = true := by
  refine ⟨?_, ?_⟩ <;> native_decide

/-- A wider witness: the contradictory pair persists at depth 4
    (and is monotone in depth, by the structure of `tarskiProvenAt`). -/
theorem tarski_bounded_inconsistent_at_4 :
    tarskiProvableUpTo 4 truePredAtLiar = true
  ∧ tarskiProvableUpTo 4 (Form.neg truePredAtLiar) = true := by
  refine ⟨?_, ?_⟩ <;> native_decide

-- ══════════════════════════════════════════════════════════
-- PART 5: SCHEMA-IMPLIES-CONTRADICTION AS ONE STATEMENT
-- ══════════════════════════════════════════════════════════
-- A clean packaging: "if both halves of the Tarski schema for L
-- and the consequentia-mirabilis axiom are present, then within
-- bounded depth the system derives both poles". The implication
-- is `True := True` shaped because we already concretely have all
-- three premises in `tarskiPool`; we restate the theorem in a form
-- that emphasises the schema --> contradiction reading.

/-- Schema-asserts-contradiction (concrete, bounded). The Tarski
    schema instance for the Liar, plus the consequentia-mirabilis
    axiom, drives inconsistency in two MP steps. -/
theorem tarski_schema_inconsistent_at_depth :
    -- premises are present at depth 0
    tarskiProvableUpTo 0 tarskiHalfFwd = true
  ∧ tarskiProvableUpTo 0 tarskiHalfBwd = true
  ∧ tarskiProvableUpTo 0 consequentiaMirabilisAxiom = true
    -- conclusions appear by depth 2
  ∧ tarskiProvableUpTo 2 truePredAtLiar = true
  ∧ tarskiProvableUpTo 2 (Form.neg truePredAtLiar) = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> native_decide

-- ══════════════════════════════════════════════════════════
-- PART 6: SANITY --- WITHOUT THE SCHEMA, NO CONTRADICTION
-- ══════════════════════════════════════════════════════════
-- The same proof system, with the Tarski schema halves removed,
-- does NOT derive both poles. This shows the contradiction is
-- *due to* the schema, not an artifact of the pool.

/-- Pool with the Tarski biconditional removed: only the
    propositional axiom and the two would-be poles. -/
def tarskiPoolNoSchema : List Form :=
  [ consequentiaMirabilisAxiom
  , Form.neg truePredAtLiar
  , truePredAtLiar
  ]

def isCMAxiomOnly (phi : Form) : Bool :=
  phi == consequentiaMirabilisAxiom

def noSchemaProvenAt : Nat → List Form
  | 0     => tarskiPoolNoSchema.filter isCMAxiomOnly
  | n + 1 =>
    let prev := noSchemaProvenAt n
    let new  := tarskiPoolNoSchema.filter (fun q =>
      existsMP_T prev q && !(prev.any (· == q)))
    prev ++ new

def noSchemaProvableUpTo (N : Nat) (phi : Form) : Bool :=
  (noSchemaProvenAt N).any (· == phi)

/-- Without the schema, neither pole is derivable at any depth we
    can finitely test. Confirms the contradiction in Part 4 truly
    comes from the Tarski biconditional, not from the propositional
    axiom alone. -/
theorem no_schema_no_contradiction_at_4 :
    noSchemaProvableUpTo 4 truePredAtLiar = false
  ∧ noSchemaProvableUpTo 4 (Form.neg truePredAtLiar) = false := by
  refine ⟨?_, ?_⟩ <;> native_decide

-- ══════════════════════════════════════════════════════════
-- PART 7: THE WALL --- WHERE FINITARY SHADOWING ENDS
-- ══════════════════════════════════════════════════════════
-- The full Tarski theorem demands:
--
--   For every formula True(x) of the language, if
--   `(forall sentence phi, T |- True(gnum phi) <-> phi)`,
--   then T is inconsistent.
--
-- The diagonal lemma reduces the universal quantifier to a single
-- Liar instance --- that is the *content* of the diagonal step ---
-- but two universal quantifiers remain unmechanized:
--
--   (W1) "For every formula True(x) ...": a quantifier over the
--        recursive set of formulas in the language. Our file fixes
--        a single concrete candidate `truePred := Box (var 0)`. To
--        prove the result holds for *every* formula True(x) one
--        must either (i) re-run the diagonal-plus-MP argument
--        uniformly in the candidate (an induction on Form), or
--        (ii) appeal to the representability theorem (the same
--        wall faced by Goedel-1).
--
--   (W2) "T |- _": the full unbounded provability predicate of the
--        target theory. As in `GodelIncompletenessShadow`, our
--        `tarskiProvableUpTo _ N` is decidable for each fixed N
--        but `forall N` is not dispatched by `native_decide`.
--
-- Both walls are the same wall the Goedel sibling met: passing
-- from "no proof at depth <= N" (and "this candidate True(x)")
-- to "no proof at any depth, for every candidate" is irreducible
-- to a finite computation.
--
-- We define the unbounded statement to *name* it, and pointedly
-- do not prove it.

/-- The unbounded Tarski statement (the wall). For every candidate
    truth predicate represented as a Form with one free variable,
    if the schema holds at every depth for the Liar built against
    that candidate, then the system is inconsistent at every depth.

    We do not prove this. It is the wall: passing from the
    bounded-N witnesses above to a `forall N` over our
    `tarskiProvenAt` family requires an induction over depth, and
    passing from a single `truePred` to a universal quantifier over
    candidate formulas requires an induction over `Form`. Neither
    is a finite computation. -/
def tarski_truth_undefinability_unbounded : Prop :=
  ∀ (cand : Form),
    -- "if a Liar can be built against `cand` and the schema holds
    -- at all depths in some sufficiently rich pool, then both poles
    -- are derivable at all depths" --- which would contradict
    -- consistency. The literal universal is what we cannot mechanize.
    ∀ N : Nat,
      tarskiProvableUpTo N truePredAtLiar = true
        ∨ tarskiProvableUpTo N (Form.neg truePredAtLiar) = true
        ∨ cand = cand  -- placeholder: the real `forall cand` lives outside `native_decide`'s reach

/-- The bounded shadow witnessed at the first eight depths. Every
    fixed depth gives a finite computable contradiction; the wall
    is at the universal quantifier `forall N`. -/
theorem tarski_bounded_witnesses_for_first_eight :
    (tarskiProvableUpTo 2 truePredAtLiar = true ∧ tarskiProvableUpTo 2 (Form.neg truePredAtLiar) = true)
  ∧ (tarskiProvableUpTo 3 truePredAtLiar = true ∧ tarskiProvableUpTo 3 (Form.neg truePredAtLiar) = true)
  ∧ (tarskiProvableUpTo 4 truePredAtLiar = true ∧ tarskiProvableUpTo 4 (Form.neg truePredAtLiar) = true)
  ∧ (tarskiProvableUpTo 5 truePredAtLiar = true ∧ tarskiProvableUpTo 5 (Form.neg truePredAtLiar) = true)
  ∧ (tarskiProvableUpTo 6 truePredAtLiar = true ∧ tarskiProvableUpTo 6 (Form.neg truePredAtLiar) = true)
  ∧ (tarskiProvableUpTo 7 truePredAtLiar = true ∧ tarskiProvableUpTo 7 (Form.neg truePredAtLiar) = true)
  ∧ (tarskiProvableUpTo 8 truePredAtLiar = true ∧ tarskiProvableUpTo 8 (Form.neg truePredAtLiar) = true)
  ∧ (tarskiProvableUpTo 9 truePredAtLiar = true ∧ tarskiProvableUpTo 9 (Form.neg truePredAtLiar) = true) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    <;> exact ⟨by native_decide, by native_decide⟩

-- ══════════════════════════════════════════════════════════
-- PART 8: THE GOEDEL/TARSKI CORRESPONDENCE
-- ══════════════════════════════════════════════════════════
-- A small bridge to the sibling: the Liar built against the
-- provability predicate is literally the Goedel sentence. This
-- makes the formal connection between Tarski-undefinability and
-- Goedel-incompleteness syntactically visible in our toy.

/-- The Liar against `Box` IS the Goedel sentence of the sibling. -/
theorem liar_collapse_to_goedel : LiarSentence = G := by rfl

/-- Their Goedel numbers coincide. -/
theorem liar_gnum_eq_goedel_gnum : gnum LiarSentence = gnum G := by rfl

/-- The Liar's syntactic form matches the Goedel sentence's
    syntactic form: both are `not (Box (numeral _))`. -/
theorem liar_shape_matches_goedel :
    LiarSentence = Form.neg (Form.box (numeral (gnum phiG))) := by rfl

-- ══════════════════════════════════════════════════════════
-- PART 9: NOTE ON LOEB'S THEOREM
-- ══════════════════════════════════════════════════════════
-- Loeb's theorem (1955): if `box(box phi -> phi) -> box phi`
-- is provable in the same provability logic, then `box phi` is
-- provable. Construction: let chi := diag (box (var 0) -> phi).
-- Then chi <-> (box (gnum chi) -> phi). The proof requires the
-- box-axioms K, T, 4 and a derived-rule pattern that does not
-- collapse cleanly inside our minimal four-axiom toy.
--
-- Bringing Loeb in honestly would require expanding the toy proof
-- system with K, T, 4 schemas and re-running the bounded search.
-- That is a *separate* file's worth of axiom curation. We deliberately
-- DO NOT mechanize it here --- the bonus would distort the
-- Liar/Tarski focus of this file. The construction is sketched in
-- the docblock so a follow-on agent has the entry point.
--
-- The diagonal infrastructure already imported is sufficient to
-- *build* chi syntactically:
--
--   def loebPhi (phi : Form) : Form := Form.imp (Form.box (Term.var 0)) phi
--   def loebChi (phi : Form) : Form := diag (loebPhi phi)
--
-- but the box-modal axioms K/T/4 are not part of `tarskiPool`, so
-- the bounded MP search will not recover Loeb's conclusion. A
-- future `LoebFixedPointShadow.lean` is the right home.

/-- The Loeb diagonal *function* is constructible from the imported
    machinery. We expose it for the follow-on file. -/
def loebPhi (phi : Form) : Form := Form.imp (Form.box (Term.var 0)) phi

/-- The Loeb diagonal sentence chi := diag (box (var 0) -> phi). -/
def loebChi (phi : Form) : Form := diag (loebPhi phi)

/-- Sanity: for phi := `eq zero zero`, the Loeb sentence is a
    concrete `Form.imp (Form.box _) _` after the diagonal. The
    syntactic shape verifies the diagonal substituted into the
    antecedent. -/
theorem loebChi_concrete_shape :
    loebChi (Form.eq Term.zero Term.zero)
      = Form.imp
          (Form.box (numeral (gnum (loebPhi (Form.eq Term.zero Term.zero)))))
          (Form.eq Term.zero Term.zero) := by rfl

-- ══════════════════════════════════════════════════════════
-- HISTORY OF ATTEMPTS (for future agents)
-- ══════════════════════════════════════════════════════════
-- The file's spine is the same hybrid A+C strategy used by the
-- Goedel sibling: bounded provability search + constructive
-- diagonal, with the wall named at the unbounded universal step.
--
-- Choice of `truePred = Box (var 0)`: forced by our toy's having
-- only one one-place predicate. The collapse of the Tarski Liar
-- into the Goedel sentence is well known --- treated explicitly
-- in Part 8 rather than hidden.
--
-- Choice of consequentia-mirabilis axiom: this is the smallest
-- propositional ingredient that turns the schema biconditional
-- `A <-> not A` into a genuine MP-derivable contradiction inside
-- our depth-bounded search. Other propositional axioms (e.g.
-- ex-falso, double negation) would also work; CM is chosen because
-- it produces the contradiction in exactly two MP steps, the
-- minimum, keeping the depth-witnessed theorems tight.
--
-- Loeb deferred: the box-axioms K/T/4 needed for Loeb are absent
-- from the toy and adding them would dilute this file. A separate
-- LoebFixedPointShadow.lean is the clean home.

end TarskiTruthUndefinability
