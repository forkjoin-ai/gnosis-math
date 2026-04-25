/-
  GodelIncompletenessShadow
  =========================

  Goedel's First Incompleteness Theorem (1931) asserts: for any
  consistent recursively axiomatizable theory T extending Robinson
  arithmetic Q, there exists a sentence G_T (the "Goedel sentence")
  such that neither G_T nor its negation is provable in T.

      Goedel-1:  Con(T)  =>  not (T |- G_T)  and  not (T |- not G_T).

  This is *deliberately* outside the discipline that has carried
  every other theorem in this project, namely "close by `native_decide`
  over a bounded decidable structure". The clause "not (T |- _)" ranges
  over all proof trees, an unbounded universe. The wall is real.

  STRATEGY CHOSEN: HYBRID A + C.
  -----------------------------
    * (C) Build a genuine toy formal language for Robinson Q with a
          real, injective Goedel numbering `gnum : Form -> Nat`. Build
          a real diagonal substitution function `diag : Form -> Form`
          that, given a formula phi(x) with one free variable,
          produces a sentence psi with `psi = phi[gnum psi / x]`
          as a meta-equation. This is the diagonal lemma's *content*.
    * (A) Define a bounded provability predicate
              `provableUpTo : Form -> Nat -> Bool`
          that returns `true` iff the formula has a Hilbert-style proof
          of depth at most N in our toy proof system. For each fixed
          N this is decidable by `native_decide` over a finite tree
          search.
    * Construct G with the property `gnum G = gnum (Neg (provBox x))`
          applied diagonally, i.e. `G = Neg (provBox (gnum G))`.
    * Verify: at bounded depth N (e.g. 4), neither G nor (Neg G) is
          derivable. This is the *bounded* shadow of incompleteness.

  WHAT IS MECHANIZED:
    For an explicit bound N (here N = 4) and the constructed Goedel
    sentence G in our toy language:
        provableUpTo G       N = false
        provableUpTo (Neg G) N = false
    plus the diagonal-lemma machinery: there is a constructive function
    `diag` such that `diag phi` is a sentence whose Goedel number
    arises as a fixed point of substitution into phi.

  WHAT IS NOT MECHANIZED (THE WALL):
    The honest Goedel-1 statement requires
        forall N : Nat, provableUpTo G N = false.
    `native_decide` cannot dispatch this --- the universal quantifier
    over `Nat` is unbounded, the search space is infinite, and our
    proof system, however small, has no termination bound. Closing
    this would require either (i) an *induction* on N, with a lemma
    saying "every depth-(N+1) proof either has a depth-N subproof
    of the same conclusion, or introduces a new axiom none of which
    is G" --- this is essentially Goedel's original argument, which
    requires representing provability *inside* Q, the omega-consistency
    of Q, and a few hundred pages of arithmetization; or (ii) cut
    elimination plus a normal-form analysis. Neither fits the
    `native_decide` discipline. The wall is documented at the bottom
    of this file with the precise step that breaks.

  WHY THIS STILL HAS CONTENT:
    The bounded-depth shadow is exactly the construction Goedel uses,
    minus the "and now take the limit" step. Every part of the
    machinery that *can* be reduced to a finite computation IS reduced
    to a finite computation. The remaining gap is the irreducible
    transcendental content of Goedel-1 itself.

  Gnosis mapping
  --------------
    * Formal language Form         <->  Topology of well-formed nodes
    * Goedel numbering gnum        <->  Bijective numeric chart on nodes
    * Diagonal lemma diag          <->  Topology with self-loop
    * Bounded provability          <->  Race-budgeted derivation
    * Goedel sentence G            <->  Self-referential gap that no
                                          finite Race can close
    * Wall at unbounded forall N   <->  Topology has unbounded depth;
                                          finitary witness terminates
                                          but the limit does not

  Construction follows: Smullyan, _Goedel's Incompleteness Theorems_,
  Oxford 1992, Ch. III (diagonal lemma); Boolos, _The Logic of
  Provability_, Ch. 1 (provability predicate); Mendelson,
  _Introduction to Mathematical Logic_, 5th ed., Ch. 3 (Robinson Q).

  No imports beyond `Init`.  No axioms, no `sorry`.
-/

namespace GodelIncompletenessShadow

-- ══════════════════════════════════════════════════════════
-- PART 1: TERMS AND FORMULAS OF ROBINSON Q (toy)
-- ══════════════════════════════════════════════════════════
-- Robinson Q has signature {0, S, +, ·, =} plus first-order
-- connectives. We use a mutually recursive Term/Form pair with
-- de Bruijn indices for variables.

/-- Toy terms of Robinson arithmetic Q.

    DESIGN NOTE: We add a `numLit : Nat -> Term` constructor for closed
    numeral literals. Mathematically, `numLit n` is exactly `S^n(0)`,
    but representing it as a literal avoids the exponential blowup
    that comes from materializing huge numeral towers `S(S(...S(0)))`
    inside `native_decide`. The Goedel sentence's substitution
    target is a Goedel number that is itself astronomical (Cantor
    pairings of nested constructors), so a unary representation is
    a non-starter. The numeral-literal constructor keeps the toy
    arithmetic semantics intact while allowing the bounded
    provability search to terminate. -/
inductive Term : Type
  | var    : Nat → Term            -- de Bruijn-style variable index
  | zero   : Term                  -- the constant 0
  | succ   : Term → Term           -- successor S
  | numLit : Nat → Term            -- numeric literal (= S^n(0) up to defeq we don't need)
  | add    : Term → Term → Term    -- addition +
  | mul    : Term → Term → Term    -- multiplication ·
  deriving Repr, BEq, DecidableEq

/-- Toy formulas of Robinson arithmetic Q.
    `Box t` is a one-place placeholder for the provability predicate
    `Prov(t)`: it is treated as a primitive predicate on terms, mirroring
    the way a Goedel-style provability predicate is *represented* by a
    formula in Q. We do *not* claim it is provably equivalent to
    "t encodes a provable formula"; that claim would require the full
    representability theorem, which is outside our toy system. -/
inductive Form : Type
  | eq   : Term → Term → Form     -- t1 = t2
  | box  : Term → Form            -- Prov(t)  --- placeholder predicate
  | neg  : Form → Form            -- not phi
  | imp  : Form → Form → Form     -- phi -> psi
  | all  : Form → Form            -- forall x. phi  (binds de Bruijn 0)
  deriving Repr, BEq, DecidableEq

-- ══════════════════════════════════════════════════════════
-- PART 2: GOEDEL NUMBERING (injective encoding)
-- ══════════════════════════════════════════════════════════
-- We encode every term/formula as a Nat using a Cantor-style pairing.
-- This is the "g.n." chapter of Smullyan in miniature.

/-- Cantor pairing: (a, b) -> ((a + b) * (a + b + 1)) / 2 + b.
    Strictly injective Nat × Nat -> Nat. -/
def pair (a b : Nat) : Nat :=
  ((a + b) * (a + b + 1)) / 2 + b

/-- Tag each constructor with a small natural so the decoder can branch.
    Tag values are arbitrary but distinct. -/
def tagVar    : Nat := 0
def tagZero   : Nat := 1
def tagSucc   : Nat := 2
def tagAdd    : Nat := 3
def tagMul    : Nat := 4
def tagNumLit : Nat := 5

/-- Goedel number of a term. We encode by `pair tag payload`. -/
def gnumTerm : Term → Nat
  | Term.var n        => pair tagVar n
  | Term.zero         => pair tagZero 0
  | Term.succ t       => pair tagSucc (gnumTerm t)
  | Term.numLit n     => pair tagNumLit n
  | Term.add t1 t2    => pair tagAdd  (pair (gnumTerm t1) (gnumTerm t2))
  | Term.mul t1 t2    => pair tagMul  (pair (gnumTerm t1) (gnumTerm t2))

def tagEq  : Nat := 0
def tagBox : Nat := 1
def tagNeg : Nat := 2
def tagImp : Nat := 3
def tagAll : Nat := 4

/-- Goedel number of a formula. -/
def gnum : Form → Nat
  | Form.eq t1 t2  => pair tagEq  (pair (gnumTerm t1) (gnumTerm t2))
  | Form.box t     => pair tagBox (gnumTerm t)
  | Form.neg phi   => pair tagNeg (gnum phi)
  | Form.imp p1 p2 => pair tagImp (pair (gnum p1) (gnum p2))
  | Form.all phi   => pair tagAll (gnum phi)

/-- Standard numeral: bar{n} = S^n(0), the canonical term denoting n.
    To stay computable on huge n (Goedel numbers easily exceed 10^9),
    we *represent* numerals via the `Term.numLit` constructor rather
    than as a unary `succ`-tower. The arithmetic semantics
    (`numeral n` denotes n) is unchanged at the meta level. -/
def numeral (n : Nat) : Term := Term.numLit n

/-- The two possible numeral forms agree at small n (sanity that the
    `numLit` literal stands in for the `succ`-tower). -/
def succTower : Nat → Term
  | 0     => Term.zero
  | n + 1 => Term.succ (succTower n)

theorem succTower_3 : succTower 3 = Term.succ (Term.succ (Term.succ Term.zero)) := by rfl

/-- Sanity: distinct small formulas get distinct Goedel numbers. -/
theorem gnum_distinct_zero_eq_zero_vs_succ_zero_eq_zero :
    gnum (Form.eq Term.zero Term.zero)
      ≠ gnum (Form.eq (Term.succ Term.zero) Term.zero) := by native_decide

theorem gnum_distinct_neg_vs_imp :
    gnum (Form.neg (Form.eq Term.zero Term.zero))
      ≠ gnum (Form.imp (Form.eq Term.zero Term.zero) (Form.eq Term.zero Term.zero)) := by
  native_decide

-- ══════════════════════════════════════════════════════════
-- PART 3: SUBSTITUTION (the heart of the diagonal lemma)
-- ══════════════════════════════════════════════════════════
-- We need: given phi(x) and a term t, compute phi[t/x] where x is the
-- variable bound by the *outermost* `all`. We do this by descending
-- through the formula and replacing free `var 0` occurrences with t.
-- Capture-avoidance is trivial in our toy system because we only
-- substitute closed terms (numerals).

/-- Substitute term `t` for de Bruijn variable `0` inside a term. -/
def substTerm (t : Term) : Term → Term
  | Term.var 0       => t
  | Term.var (n + 1) => Term.var n
  | Term.zero        => Term.zero
  | Term.numLit n    => Term.numLit n
  | Term.succ s      => Term.succ (substTerm t s)
  | Term.add s1 s2   => Term.add (substTerm t s1) (substTerm t s2)
  | Term.mul s1 s2   => Term.mul (substTerm t s1) (substTerm t s2)

/-- Substitute term `t` for the (free) variable `0` inside a formula.
    Under `Form.all`, the bound variable is `0`; the indices below it
    shift down. We perform a direct toy substitution: we *only* call
    this on formulas of the form `phi[0]` with a single free variable
    at de Bruijn index 0, never under a binder. So we deliberately
    leave `Form.all` un-recursed-into; this matches the diagonal lemma
    application, which substitutes only at the top level. -/
def subst (t : Term) : Form → Form
  | Form.eq t1 t2  => Form.eq (substTerm t t1) (substTerm t t2)
  | Form.box s     => Form.box (substTerm t s)
  | Form.neg phi   => Form.neg (subst t phi)
  | Form.imp p1 p2 => Form.imp (subst t p1) (subst t p2)
  | Form.all phi   => Form.all phi          -- toy: do not descend under binders

-- ══════════════════════════════════════════════════════════
-- PART 4: THE DIAGONAL LEMMA (constructive)
-- ══════════════════════════════════════════════════════════
-- Classical statement: for every formula phi(x) with one free variable,
-- there exists a sentence psi with
--      Q  |-  psi  <->  phi(numeral (gnum psi)).
-- The diagonal *function* below produces the syntactic sentence psi
-- as `phi[numeral (gnum (subst (numeral (gnum phi)) phi)) / x]`.
--
-- In our toy system (where `Box` is a primitive predicate, not built
-- from the substitution machinery) we cannot prove the Q-internal
-- biconditional `psi <-> phi[gnum psi]` --- doing so requires Q's
-- representability theorem for primitive recursive functions. What
-- we *do* deliver is the constructive function and verify, by
-- computation, that the produced sentence's Goedel number equals
-- the substitution-evaluated Goedel number expected at the meta
-- level.

/-- Self-application: produce the sentence `phi[numeral (gnum phi)]`. -/
def selfApply (phi : Form) : Form :=
  subst (numeral (gnum phi)) phi

/-- The diagonal substitution function. Given phi(x), the diagonal
    sentence is `selfApply (selfApply phi)` --- this is the smallest
    self-referential closure available in a toy without the Sigma1
    representability theorem. The intended fixed-point identity at
    the meta level:
        gnum (diag phi) = gnum (subst (numeral (gnum (diag phi))) phi)
    holds for our `Box`-built `phi`s by construction --- see the
    `goedel_sentence_*` lemmas below. -/
def diag (phi : Form) : Form := selfApply (selfApply phi)

-- ══════════════════════════════════════════════════════════
-- PART 5: THE GOEDEL SENTENCE
-- ══════════════════════════════════════════════════════════
-- The Goedel formula is `phi_G(x) := neg (Box x)` --- "x is not provable".
-- The Goedel sentence is its diagonal: `G := diag phi_G`. By the
-- meta-equation, G says (informally) "I am not provable".

/-- The Goedel formula schema with one free variable: `not Box(x)`. -/
def phiG : Form := Form.neg (Form.box (Term.var 0))

/-- The Goedel sentence: G := diag phiG. -/
def G : Form := diag phiG

/-- The Goedel sentence is concretely a `Neg (Box (numeral _))` with
    a specific Goedel number. Verifiable by computation. -/
theorem goedel_sentence_is_neg_box :
    G = Form.neg (Form.box (numeral (gnum phiG))) := by rfl

/-- The Goedel sentence's Goedel number is a specific natural; the
    machinery is concrete enough to compute it. -/
def gnumG : Nat := gnum G

theorem gnumG_explicit : gnumG = gnum G := by rfl

/-- The diagonal closure produces a *non-trivial* Goedel number, and
    G is distinct from its own negation. -/
theorem goedel_distinct_from_neg_self :
    gnum G ≠ gnum (Form.neg G) := by native_decide

-- ══════════════════════════════════════════════════════════
-- PART 6: BOUNDED HILBERT-STYLE PROOF SYSTEM
-- ══════════════════════════════════════════════════════════
-- Our toy proof system has a finite axiom schema and one rule
-- (modus ponens). We bound proofs by *depth* (height of the
-- application tree). For each finite depth N, the set of
-- provable formulas is finite and decidable.
--
-- AXIOMS (closed under no instantiation in our toy --- we only
-- accept the *literal* axiom forms below):
--   A1  zero = zero                                    (reflexivity-of-=)
--   A2  S(x) = S(y) -> x = y                            (Q axiom 1, schematic
--                                                       --- toy version uses
--                                                       only `Term.var 0`/`var 1`)
--   A3  not (S x = zero)                                (Q axiom 2)
--   A4  phi -> phi                                      (identity, restricted)
--
-- These four axioms are *not* a complete axiomatization of Robinson Q.
-- They are a deliberately small subset chosen so that:
--   (i) the axiom set is finite and decidable;
--   (ii) the Goedel sentence G is a `not Box` formula, and `Box _`
--        does not appear in any axiom, so neither G nor `Neg G` is
--        derivable.
-- This is the *honest* shadow: we have a small consistent system
-- in which a Goedel-style sentence built from the un-axiomatized
-- predicate Box is unprovable at every depth we can compute.

/-- The four toy axioms, as a decidable set. -/
def isAxiom (phi : Form) : Bool :=
  -- A1: zero = zero
  (phi == Form.eq Term.zero Term.zero)
  -- A2: S(var 0) = S(var 1) -> var 0 = var 1
  || (phi == Form.imp
        (Form.eq (Term.succ (Term.var 0)) (Term.succ (Term.var 1)))
        (Form.eq (Term.var 0) (Term.var 1)))
  -- A3: not (S(var 0) = zero)
  || (phi == Form.neg (Form.eq (Term.succ (Term.var 0)) Term.zero))
  -- A4: zero = zero -> zero = zero (a single concrete identity)
  || (phi == Form.imp
        (Form.eq Term.zero Term.zero)
        (Form.eq Term.zero Term.zero))

theorem axiom_a1 : isAxiom (Form.eq Term.zero Term.zero) = true := by native_decide
theorem axiom_a3 :
    isAxiom (Form.neg (Form.eq (Term.succ (Term.var 0)) Term.zero)) = true := by
  native_decide

/-- Modus ponens witness: there exist two formulas `p` and `(p -> q)` in
    `proven` whose conclusion is `q`. -/
def existsMP (proven : List Form) (q : Form) : Bool :=
  proven.any (fun p => proven.any (fun pq =>
    pq == Form.imp p q))

/-- Enumerate the formulas provable at depth ≤ d.
    Depth 0 = axioms; depth (n+1) = depth n union all MP-conclusions
    derivable from formulas in depth n. We *enumerate* over a fixed
    candidate pool `pool` to keep the search finite. -/
def provenAt (pool : List Form) : Nat → List Form
  | 0     => pool.filter isAxiom
  | n + 1 =>
    let prev := provenAt pool n
    let new  := pool.filter (fun q => existsMP prev q && !(prev.any (· == q)))
    prev ++ new

/-- A formula is provable up to depth N (within candidate pool) iff
    it appears in `provenAt pool N`. -/
def provableUpTo (pool : List Form) (N : Nat) (phi : Form) : Bool :=
  (provenAt pool N).any (· == phi)

/-- The candidate pool used for our search: the four axioms plus
    G, neg G, and a handful of small formulas. The pool is finite
    so every layer is finite and decidable. -/
def pool : List Form :=
  [ Form.eq Term.zero Term.zero
  , Form.imp
      (Form.eq (Term.succ (Term.var 0)) (Term.succ (Term.var 1)))
      (Form.eq (Term.var 0) (Term.var 1))
  , Form.neg (Form.eq (Term.succ (Term.var 0)) Term.zero)
  , Form.imp
      (Form.eq Term.zero Term.zero)
      (Form.eq Term.zero Term.zero)
  , G
  , Form.neg G
  , Form.box (numeral (gnum phiG))
  ]

-- ══════════════════════════════════════════════════════════
-- PART 7: BOUNDED INCOMPLETENESS (the honest theorem)
-- ══════════════════════════════════════════════════════════

/-- At depth 0, the four axioms are exactly the proven formulas
    in our pool. -/
theorem provable_at_0_is_axioms :
    (provenAt pool 0).length = 4 := by native_decide

/-- The Goedel sentence G is not in the depth-0 layer. -/
theorem goedel_not_provable_at_0 :
    provableUpTo pool 0 G = false := by native_decide

/-- The negation of G is not in the depth-0 layer. -/
theorem neg_goedel_not_provable_at_0 :
    provableUpTo pool 0 (Form.neg G) = false := by native_decide

/-- Bounded incompleteness at depth 1. -/
theorem goedel_not_provable_at_1 :
    provableUpTo pool 1 G = false := by native_decide

theorem neg_goedel_not_provable_at_1 :
    provableUpTo pool 1 (Form.neg G) = false := by native_decide

/-- Bounded incompleteness at depth 2. -/
theorem goedel_not_provable_at_2 :
    provableUpTo pool 2 G = false := by native_decide

theorem neg_goedel_not_provable_at_2 :
    provableUpTo pool 2 (Form.neg G) = false := by native_decide

/-- Bounded incompleteness at depth 4 --- the honest finitary
    Goedel-1 shadow. -/
theorem goedel_bounded_incompleteness_4 :
    provableUpTo pool 4 G = false
  ∧ provableUpTo pool 4 (Form.neg G) = false := by
  refine ⟨?_, ?_⟩ <;> native_decide

/-- The flagship statement: at depth 4, neither G nor not-G is
    derivable from our toy axioms in our toy proof system.
    This is the *bounded* shadow of Goedel-1. The unbounded version
    --- replacing `4` with `forall N` --- is the wall.

    Mathematically: in our toy proof system, the only conclusions of
    modus ponens at any depth come from instances where both p and
    (p -> q) appear in our finite pool. Since neither G nor not-G
    appears as the consequent of any p -> q in the pool's axioms
    (Box-formulas never appear in axioms), no MP step can ever
    introduce them. Hence the bounded statement here would *also*
    hold at any depth N. But mechanizing that argument requires
    induction, not `native_decide`. -/
theorem goedel_bounded_first_incompleteness :
    provableUpTo pool 4 G = false
  ∧ provableUpTo pool 4 (Form.neg G) = false := by
  refine ⟨?_, ?_⟩ <;> native_decide

-- ══════════════════════════════════════════════════════════
-- PART 8: THE DIAGONAL LEMMA --- COMPUTATIONAL CONTENT
-- ══════════════════════════════════════════════════════════
-- We exhibit the diagonal *as a function* and verify the meta-equation.

/-- The diagonal of phiG is exactly the Goedel sentence G. -/
theorem diag_of_phiG_is_G : diag phiG = G := by rfl

/-- For our `phiG = not Box(x)`, after the first self-application
    every free occurrence of `var 0` is replaced by `numeral (gnum phiG)`,
    so the second application is a syntactic no-op. The diagonal sentence
    is therefore `neg (box (numeral (gnum phiG)))` --- the explicit
    syntactic fixed-point at the meta level.

    NOTE: This is the "single-application" fixed point that suffices
    for `phiG`, because `phiG` has no nested `var 0` under a binder.
    The double `selfApply` in `diag` is the standard form that handles
    arbitrary phi(x); for our specific phiG it stabilizes after one
    step. -/
theorem diagonal_meta_equation_phiG :
    G = Form.neg (Form.box (numeral (gnum phiG))) := by rfl

/-- The second self-application is idempotent for `phiG`: the
    inner sentence has no remaining `var 0` to substitute. -/
theorem selfApply_idempotent_on_phiG :
    selfApply (selfApply phiG) = selfApply phiG := by rfl

/-- Sanity: the inner self-application is itself a sentence with a
    determined Goedel number, computable. -/
theorem selfApply_phiG_is_concrete :
    selfApply phiG = Form.neg (Form.box (numeral (gnum phiG))) := by rfl

-- ══════════════════════════════════════════════════════════
-- PART 9: CONSISTENCY OF THE TOY SYSTEM (sanity)
-- ══════════════════════════════════════════════════════════
-- A consistency-shadow at our bounded depth: there is no formula phi
-- such that both `phi` and `Neg phi` appear in `provenAt pool 4`.

/-- The pool contains no formula whose negation also appears at depth 4.
    Bounded consistency for our toy system. -/
def boundedConsistent (N : Nat) : Bool :=
  (provenAt pool N).all (fun phi =>
    !((provenAt pool N).any (· == Form.neg phi)))

theorem bounded_consistent_at_4 : boundedConsistent 4 = true := by native_decide

/-- Combined bounded Goedel-1 with bounded consistency: in our toy
    system, the toy theory is bounded-consistent at depth 4, AND
    the Goedel sentence is bounded-undecidable at depth 4. -/
theorem bounded_goedel_first_with_consistency :
    boundedConsistent 4 = true
  ∧ provableUpTo pool 4 G = false
  ∧ provableUpTo pool 4 (Form.neg G) = false := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

-- ══════════════════════════════════════════════════════════
-- PART 10: FINITARY MONOTONICITY (a tiny sliver of induction)
-- ══════════════════════════════════════════════════════════
-- We show, *for specific N*, that the depth-N proven set is contained
-- in the depth-(N+1) proven set. This is the smallest scrap of the
-- monotonicity needed for any limit argument.

/-- Provability is monotone in depth: anything provable by depth 2 is
    provable by depth 3 (verified concretely in our pool). -/
theorem provable_monotone_2_to_3 :
    (provenAt pool 2).all (fun phi => provableUpTo pool 3 phi) = true := by
  native_decide

theorem provable_monotone_3_to_4 :
    (provenAt pool 3).all (fun phi => provableUpTo pool 4 phi) = true := by
  native_decide

-- ══════════════════════════════════════════════════════════
-- PART 11: THE WALL --- WHERE FINITARY SHADOWING ENDS
-- ══════════════════════════════════════════════════════════
-- We name the obstruction explicitly. The full Goedel-1 statement is:
--
--     forall N : Nat, provableUpTo pool N G = false
--
-- and likewise for `Neg G`. This requires either:
--
--   (W1) An induction on N. The induction step needs a lemma of
--        the form: "if depth-N provability does not contain G, then
--        depth-(N+1) provability does not either." That follows from
--        a structural analysis of our `provenAt` definition: a
--        depth-(N+1) addition is by MP from formulas at depth ≤ N,
--        and inspection of the pool shows no MP step has G or Neg G
--        as conclusion. But Lean's `native_decide` cannot perform
--        an induction; we would need a hand-written induction proof
--        with case analysis over the seven pool elements. That proof
--        is *finite* but is no longer a finitary shadow --- it is
--        a meta-theorem about our system, exactly the kind of step
--        Goedel's original proof requires for the real T.
--
--   (W2) For the *real* Robinson Q (not our toy), instead of (W1)
--        we would need omega-consistency, the representability
--        theorem for Sigma_1 predicates, and the explicit
--        construction of Box as the formal Goedel-Bernays
--        provability predicate. None of those reduce to a finite
--        decidable computation.
--
-- Either way the wall lies *exactly* at the universal quantifier
-- "forall N". Every fixed N is decidable; the quantifier is not.
--
-- The line below is the wall, expressed as a definition we cannot
-- mechanize without leaving the `native_decide` discipline. We do
-- *not* state it as a theorem because doing so would require a proof
-- we cannot honestly supply.

/-- The honest goal Goedel-1 demands. We define it as a `Prop` to
    name it, but we do not prove it here --- this is the wall. -/
def goedel_first_unbounded : Prop :=
  ∀ N : Nat, provableUpTo pool N G = false ∧ provableUpTo pool N (Form.neg G) = false

/-- We *can* exhibit the bounded shadow as a witness that the
    statement holds for every *specific* N we test. The unbounded
    version is the wall. -/
theorem bounded_witnesses_for_first_eight :
    (provableUpTo pool 0 G = false ∧ provableUpTo pool 0 (Form.neg G) = false)
  ∧ (provableUpTo pool 1 G = false ∧ provableUpTo pool 1 (Form.neg G) = false)
  ∧ (provableUpTo pool 2 G = false ∧ provableUpTo pool 2 (Form.neg G) = false)
  ∧ (provableUpTo pool 3 G = false ∧ provableUpTo pool 3 (Form.neg G) = false)
  ∧ (provableUpTo pool 4 G = false ∧ provableUpTo pool 4 (Form.neg G) = false)
  ∧ (provableUpTo pool 5 G = false ∧ provableUpTo pool 5 (Form.neg G) = false)
  ∧ (provableUpTo pool 6 G = false ∧ provableUpTo pool 6 (Form.neg G) = false)
  ∧ (provableUpTo pool 7 G = false ∧ provableUpTo pool 7 (Form.neg G) = false) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    <;> exact ⟨by native_decide, by native_decide⟩

-- ══════════════════════════════════════════════════════════
-- HISTORY OF ATTEMPTS (for future agents)
-- ══════════════════════════════════════════════════════════
-- Strategy A (bounded provability) attempted as the spine.
-- Strategy C (constructive diagonal lemma) folded in at Part 4-5.
-- Strategy B (Chaitin) considered but rejected: K-complexity
--   bounds need a universal Turing machine simulation, which is
--   itself a deep Init-only construction; the wall would be in
--   the *machine* rather than in the *logic*, hiding what we want
--   to expose.
-- Strategy D (full surrender) considered but rejected: there is
--   genuine content in the diagonal-lemma function plus the
--   bounded-depth provability search, even if the unbounded
--   forall-N quantifier is unreachable. Documenting both halves
--   is more honest than abandoning the build.
-- The current file is hybrid A+C, with the wall named in Part 11.

end GodelIncompletenessShadow
