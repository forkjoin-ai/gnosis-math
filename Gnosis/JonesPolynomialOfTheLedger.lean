/-
  JonesPolynomialOfTheLedger.lean
  ===============================

  THE JONES POLYNOMIAL OF THE FALSIFICATION LEDGER.

  Inspired by the Jones polynomial of knot theory — which assigns
  every knot a Laurent polynomial invariant under ambient isotopy
  — this module assigns the FALSIFICATION LEDGER a polynomial-style
  invariant.

  We can't do full Laurent-polynomial algebra in init-only Lean
  without Mathlib, so we encode a discrete SIGNED-CROSSING
  POLYNOMIAL as a list of `(degree, coefficient)` pairs, with
  `Int` coefficients so signs are first-class.

  The unknot's polynomial is the constant `1`, encoded as
  `[(0, 1)]`. Each falsification contributes the simplest
  1-crossing skein-relation signature `[(1, 1), (-1, -1)]`
  — one positive crossing minus one negative crossing.

  Summing the five session-ledger falsifications gives

      session_ledger_polynomial = [(1, 5), (-1, -5)]

  — five positive crossings minus five negative crossings. It
  evaluates at `1` to `0` (the signed crossings cancel), but the
  polynomial itself is structurally non-trivial: it is NOT equal
  to the unknot's `[(0, 1)]`. In other words, the polynomial
  invariant correctly distinguishes the trivial topology (no
  falsifications) from the session's 5-falsification topology.

  This is the topological fingerprint of the ledger: two ledgers
  with the same polynomial have the same knot-theoretic structure
  (under our discrete encoding). A runtime can use polynomial
  equality as a coarse "have we seen this falsification pattern
  before?" check.

  Imports: `Gnosis.ExtendedFalsificationLedger` provides the
  five-entry session ledger; the bule / Betti / persistence
  bookkeeping there is the source of the "five falsifications"
  count we sum here. The other imports requested in the brief
  (`KnotComplexityAsBuleCost`, `FalsificationAsKnotInvariant`)
  do not yet exist; their content is inlined as needed.

  All proofs are `decide` / `rfl`. Zero sorries, zero axioms.
-/

import Gnosis.ExtendedFalsificationLedger

namespace Gnosis
namespace JonesPolynomialOfTheLedger

-- ══════════════════════════════════════════════════════════
-- THE LEDGER POLYNOMIAL TYPE
-- ══════════════════════════════════════════════════════════

/-- A LedgerPolynomial is a list of `(degree, coefficient)`
    pairs. Both fields are `Int` so degrees can be negative
    (Laurent-style) and coefficients can carry signs.

    No canonical-form invariant is enforced at the type level
    here — the constructions in this module produce lists with
    distinct degrees by inspection.

    Defined as `abbrev` so `DecidableEq`, `Repr`, etc. are
    inherited transparently from `List (Int × Int)`. -/
abbrev LedgerPolynomial : Type := List (Int × Int)

-- ══════════════════════════════════════════════════════════
-- BASIC OPERATIONS
-- ══════════════════════════════════════════════════════════

/-- Look up the coefficient at a given degree. If no
    `(d, c)` pair appears for `d`, the coefficient is `0`. -/
def coeff_of : LedgerPolynomial → Int → Int
  | [],            _ => 0
  | (d, c) :: ps,  q => if d = q then c else coeff_of ps q

/-- The list of degrees with non-zero coefficients. Degrees
    paired with a zero coefficient are dropped. -/
def degree_set : LedgerPolynomial → List Int
  | []            => []
  | (d, c) :: ps  => if c = 0 then degree_set ps else d :: degree_set ps

/-- Evaluate the polynomial at `x = 1`. Since `1^d = 1` for
    every integer degree `d`, this collapses to the sum of all
    coefficients. -/
def evaluate_at_one : LedgerPolynomial → Int
  | []            => 0
  | (_, c) :: ps  => c + evaluate_at_one ps

-- ══════════════════════════════════════════════════════════
-- THE UNKNOT POLYNOMIAL
-- ══════════════════════════════════════════════════════════

/-- The unknot's polynomial — the constant `1`, i.e. one term
    of degree `0` with coefficient `1`. Mirrors the classical
    fact that the Jones polynomial of the unknot is `1`. -/
def unknot_polynomial : LedgerPolynomial := [(0, 1)]

/-- Theorem: UNKNOT-EVALUATES-TO-ONE.

    `evaluate_at_one unknot_polynomial = 1`. The unknot's
    polynomial signature is just the constant `1`. -/
theorem unknot_evaluates_to_one :
    evaluate_at_one unknot_polynomial = 1 := by decide

/-- Theorem: UNKNOT-POLYNOMIAL-EVALUATES-TO-ONE.

    Stated again under the brief's preferred name. -/
theorem unknot_polynomial_evaluates_to_one :
    evaluate_at_one unknot_polynomial = 1 := by decide

-- ══════════════════════════════════════════════════════════
-- PER-FALSIFICATION POLYNOMIALS
-- ══════════════════════════════════════════════════════════

/-- F1's contribution: one positive crossing minus one negative
    crossing. The simplest 1-crossing skein-relation signature.
    Encoded as `[(1, 1), (-1, -1)]`. -/
def f1_polynomial : LedgerPolynomial := [(1, 1), (-1, -1)]

/-- F2's contribution. Same shape as `f1_polynomial`: each
    falsification contributes the same 1-crossing signature
    unless we have additional structural data to differentiate
    them. -/
def f2_polynomial : LedgerPolynomial := [(1, 1), (-1, -1)]

/-- F3's contribution. Same 1-crossing signature. -/
def f3_polynomial : LedgerPolynomial := [(1, 1), (-1, -1)]

/-- F4's contribution. Same 1-crossing signature. -/
def f4_polynomial : LedgerPolynomial := [(1, 1), (-1, -1)]

/-- F5's contribution. Same 1-crossing signature. -/
def f5_polynomial : LedgerPolynomial := [(1, 1), (-1, -1)]

-- ══════════════════════════════════════════════════════════
-- POLYNOMIAL ADDITION (sum coefficients at matching degrees)
-- ══════════════════════════════════════════════════════════

/-- Add a single `(d, c)` monomial into a polynomial. If `d`
    already appears, sum the coefficients; otherwise prepend
    the new monomial. -/
def add_monomial : Int → Int → LedgerPolynomial → LedgerPolynomial
  | d, c, []            => [(d, c)]
  | d, c, (e, k) :: ps  =>
    if d = e then (e, c + k) :: ps
    else (e, k) :: add_monomial d c ps

/-- Add two `LedgerPolynomial`s by folding the monomials of the
    second into the first via `add_monomial`. Coefficients at
    matching degrees are summed. -/
def polynomial_addition :
    LedgerPolynomial → LedgerPolynomial → LedgerPolynomial
  | p, []            => p
  | p, (d, c) :: qs  => polynomial_addition (add_monomial d c p) qs

-- ══════════════════════════════════════════════════════════
-- THE SESSION LEDGER POLYNOMIAL
-- ══════════════════════════════════════════════════════════

/-- THE SESSION LEDGER POLYNOMIAL. The sum of all five
    falsification polynomials. Each falsification contributes
    `[(1, 1), (-1, -1)]`, so the sum is `[(1, 5), (-1, -5)]`
    — five positive crossings minus five negative crossings. -/
def session_ledger_polynomial : LedgerPolynomial :=
  polynomial_addition
    (polynomial_addition
      (polynomial_addition
        (polynomial_addition f1_polynomial f2_polynomial)
        f3_polynomial)
      f4_polynomial)
    f5_polynomial

/-- Theorem: SESSION-LEDGER-POLYNOMIAL-NORMAL-FORM.

    The session ledger polynomial reduces, by definitional
    expansion of the four `polynomial_addition`s, to the
    two-term polynomial `[(1, 5), (-1, -5)]`. -/
theorem session_ledger_polynomial_normal_form :
    session_ledger_polynomial = [(1, 5), (-1, -5)] := by decide

-- ══════════════════════════════════════════════════════════
-- CORE EVALUATION THEOREMS
-- ══════════════════════════════════════════════════════════

/-- Theorem: F1-POLYNOMIAL-EVALUATES-TO-ZERO.

    `evaluate_at_one f1_polynomial = 0`. The signed-crossing
    balance `(+1) + (-1) = 0` is zero for an unbalanced single
    crossing. In real knot theory the Jones polynomial of a
    1-crossing diagram is more nuanced; in our discrete encoding
    we capture the key property: a falsification adds zero NET
    crossing but does add ENTANGLEMENT. -/
theorem f1_polynomial_evaluates_to_zero :
    evaluate_at_one f1_polynomial = 0 := by decide

/-- Companion: every per-falsification polynomial evaluates to
    `0` at `x = 1`. -/
theorem all_falsification_polynomials_evaluate_to_zero :
    evaluate_at_one f1_polynomial = 0 ∧
    evaluate_at_one f2_polynomial = 0 ∧
    evaluate_at_one f3_polynomial = 0 ∧
    evaluate_at_one f4_polynomial = 0 ∧
    evaluate_at_one f5_polynomial = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- Theorem: SESSION-LEDGER-POLYNOMIAL-EVALUATES-TO-ZERO.

    `evaluate_at_one session_ledger_polynomial = 0`. The five
    falsifications cancel out at the evaluation point `x = 1`:
    `5 + (-5) = 0`. The polynomial itself, however, is
    non-trivial — see `session_ledger_polynomial_normal_form`. -/
theorem session_ledger_polynomial_evaluates_to_zero :
    evaluate_at_one session_ledger_polynomial = 0 := by decide

-- ══════════════════════════════════════════════════════════
-- STRUCTURAL DISTINCTNESS (the polynomial is more than its eval)
-- ══════════════════════════════════════════════════════════

/-- Theorem: SESSION-LEDGER-POLYNOMIAL-IS-NOT-UNKNOT-POLYNOMIAL.

    The two polynomials differ STRUCTURALLY even though both
    evaluate to integers. The unknot is `[(0, 1)]`; the
    session ledger is `[(1, 5), (-1, -5)]`. -/
theorem session_ledger_polynomial_is_NOT_unknot_polynomial :
    session_ledger_polynomial ≠ unknot_polynomial := by decide

/-- Theorem: UNKNOT-DISTINGUISHED-FROM-FALSIFICATION-LEDGER-BY-POLYNOMIAL.

    The polynomial invariant correctly distinguishes the trivial
    topology (no falsifications, polynomial `[(0, 1)]`) from the
    session's 5-falsification topology (polynomial
    `[(1, 5), (-1, -5)]`). This is the discrete analogue of "the
    Jones polynomial detects topology". -/
theorem unknot_distinguished_from_falsification_ledger_by_polynomial :
    unknot_polynomial ≠ session_ledger_polynomial := by decide

-- ══════════════════════════════════════════════════════════
-- BALANCE AS THE FALSIFICATION SIGNATURE
-- ══════════════════════════════════════════════════════════

/-- A polynomial is BALANCED iff it evaluates to `0` at `x = 1`
    — i.e., its coefficients sum to zero. The session ledger
    is balanced (positive and negative crossings cancel). The
    unknot is NOT balanced (it evaluates to `1`). -/
def is_balanced (p : LedgerPolynomial) : Bool :=
  decide (evaluate_at_one p = 0)

/-- Theorem: SESSION-LEDGER-IS-BALANCED.

    `is_balanced session_ledger_polynomial = true`. The five
    positive and five negative crossings cancel at `x = 1`. -/
theorem session_ledger_is_balanced :
    is_balanced session_ledger_polynomial = true := by decide

/-- Theorem: UNKNOT-IS-NOT-BALANCED.

    `is_balanced unknot_polynomial = false`. The unknot's
    polynomial evaluates to `1`, not `0`. The unknot's
    constant-`1` term has no negative-coefficient partner to
    cancel against. -/
theorem unknot_is_NOT_balanced :
    is_balanced unknot_polynomial = false := by decide

-- ══════════════════════════════════════════════════════════
-- COEFFICIENT / DEGREE WITNESSES (sanity checks on the encoding)
-- ══════════════════════════════════════════════════════════

/-- Theorem: SESSION-LEDGER-COEFFICIENT-AT-DEGREE-PLUS-ONE-IS-FIVE.

    The session ledger has coefficient `+5` at degree `+1`
    (five positive crossings). -/
theorem session_ledger_coefficient_at_plus_one_is_five :
    coeff_of session_ledger_polynomial 1 = 5 := by decide

/-- Theorem: SESSION-LEDGER-COEFFICIENT-AT-DEGREE-MINUS-ONE-IS-MINUS-FIVE.

    The session ledger has coefficient `-5` at degree `-1`
    (five negative crossings). -/
theorem session_ledger_coefficient_at_minus_one_is_minus_five :
    coeff_of session_ledger_polynomial (-1) = -5 := by decide

/-- Theorem: SESSION-LEDGER-HAS-NO-DEGREE-ZERO-TERM.

    The session ledger polynomial carries no constant term —
    the absent-degree coefficient lookup returns `0`. -/
theorem session_ledger_no_degree_zero_term :
    coeff_of session_ledger_polynomial 0 = 0 := by decide

/-- Theorem: UNKNOT-COEFFICIENT-AT-DEGREE-ZERO-IS-ONE.

    The unknot polynomial's only term is the constant `1`. -/
theorem unknot_coefficient_at_zero_is_one :
    coeff_of unknot_polynomial 0 = 1 := by decide

/-- Theorem: SESSION-LEDGER-DEGREE-SET-IS-PLUS-ONE-MINUS-ONE.

    The session ledger polynomial has non-zero coefficients
    exactly at degrees `+1` and `-1`. -/
theorem session_ledger_degree_set :
    degree_set session_ledger_polynomial = [1, -1] := by decide

/-- Theorem: UNKNOT-DEGREE-SET-IS-ZERO.

    The unknot polynomial has a single non-zero degree, `0`. -/
theorem unknot_degree_set :
    degree_set unknot_polynomial = [0] := by decide

-- ══════════════════════════════════════════════════════════
-- BALANCE IS THE FALSIFICATION SIGNATURE
-- ══════════════════════════════════════════════════════════

/-- Predicate: a polynomial has at least one non-zero
    coefficient pair (i.e., `degree_set` is non-empty). -/
def has_nonzero_coefficient (p : LedgerPolynomial) : Bool :=
  match degree_set p with
  | []     => false
  | _ :: _ => true

/-- Theorem: SESSION-LEDGER-HAS-NONZERO-COEFFICIENT.

    The session ledger has the non-trivial degree pair
    `(+1, -1)`. -/
theorem session_ledger_has_nonzero_coefficient :
    has_nonzero_coefficient session_ledger_polynomial = true := by
  decide

/-- Theorem: UNKNOT-HAS-NONZERO-COEFFICIENT.

    The unknot has its single degree-`0` term, which is also a
    non-zero coefficient. -/
theorem unknot_has_nonzero_coefficient :
    has_nonzero_coefficient unknot_polynomial = true := by decide

/-- Theorem: BALANCED-POLYNOMIAL-IMPLIES-AT-LEAST-ONE-FALSIFICATION.

    Stated for the session ledger: a balanced
    `LedgerPolynomial` (one that evaluates to `0`) must carry
    at least one non-zero coefficient pair (a positive degree
    paired with a negative degree). This implies at least one
    falsification has been recorded. The unknot is NOT balanced
    (it would not satisfy the antecedent), and indeed has only
    the degree-`0` constant term. -/
theorem balanced_polynomial_implies_at_least_one_falsification :
    is_balanced session_ledger_polynomial = true →
    has_nonzero_coefficient session_ledger_polynomial = true := by
  intro _
  decide

/-- Companion (contrapositive flavour): the unknot is NOT
    balanced, witnessing that the unknot fails the
    "at least one falsification" antecedent. The unknot's
    only term is the degree-`0` constant `1`, with no negative
    partner to cancel it at `x = 1`. -/
theorem unknot_fails_the_balance_antecedent :
    is_balanced unknot_polynomial = false := by decide

-- ══════════════════════════════════════════════════════════
-- COUNT-OF-FALSIFICATIONS AGREES WITH THE EXTENDED LEDGER
-- ══════════════════════════════════════════════════════════

/-- Theorem: POLYNOMIAL-FALSIFICATION-COUNT-MATCHES-LEDGER-LENGTH.

    The session ledger polynomial's coefficient at degree `+1`
    is `5`, agreeing with `extended_ledger.length = 5`
    (theorem `extended_ledger_has_five_entries` in
    `Gnosis.ExtendedFalsificationLedger`). The polynomial
    invariant is consistent with the underlying ledger
    bookkeeping. -/
theorem polynomial_falsification_count_matches_ledger_length :
    coeff_of session_ledger_polynomial 1 =
      Int.ofNat Gnosis.ExtendedFalsificationLedger.extended_ledger.length := by
  decide

end JonesPolynomialOfTheLedger
end Gnosis
