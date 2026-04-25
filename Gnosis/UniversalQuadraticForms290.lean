/-
  UniversalQuadraticForms290
  ==========================

  Bhargava and Hanke 2005, _Universal quadratic forms and the
  290-theorem_: a positive-definite integer-matrix quadratic form Q
  represents every positive integer iff it represents the explicit
  finite set
        S_290 = {1, 2, 3, 5, 6, 7, 10, 13, 14, 15, 17, 19, 21, 22,
                 23, 26, 29, 30, 31, 34, 35, 37, 42, 58, 93, 110,
                 145, 203, 290}.
  An earlier Conway-Schneeberger 1993 result (the 15-theorem) gives
  the same statement for forms whose Gram matrix has integer
  entries: representing 1..15 (and a refined critical set inside it)
  implies representing all positive integers.

  Both theorems are research-grade results --- the implications
  "represents the critical set => represents everything" require
  extensive case analysis on lattice geometry that is far outside
  `native_decide`. The country-church discipline forbids
  `import Mathlib`, so even the supporting infrastructure is
  unavailable.

  STRATEGY: HEROIC-FINITE WITNESS PRODUCTION + CRITICAL-SET CHECKS.
  -----------------------------------------------------------------
  The shadow we mechanize:

    * Lagrange's four-square theorem at scale 290. For every
      n in {1, ..., 290}, exhibit explicit (a, b, c, d) with
      a^2 + b^2 + c^2 + d^2 = n. Verified by `native_decide` on a
      bounded search.

    * 15-theorem witness. The 15 critical numbers are
        {1, 2, 3, 5, 6, 7, 10, 13, 14, 15}.
      Verify the four-square form represents every member.

    * 290-theorem witness. The 29 critical numbers are
        S_290 above. Verify the four-square form represents every
      member.

    * The full Bhargava-Hanke implication ("represents S_290 =>
      represents all positive integers") is the LOGICAL/DEEP wall:
      its proof involves explicit escalator-form classification and
      Siegel-mass estimates. Not mechanized here. Documented as the
      wall.

    * Bonus: confirm that the four-square form represents every
      positive integer up to 1000 (Lagrange at industrial scale).

  Gnosis mapping
  --------------
    * Quadratic form Q(x,y,z,w) = x^2+y^2+z^2+w^2
                                  <->  Topology with four free
                                       branch parameters
    * Representation a^2+b^2+c^2+d^2 = n
                                  <->  Race-budget allocation
                                       summing to n
    * Bounded witness search      <->  Fork/race over (a,b,c,d) up
                                       to floor(sqrt n)
    * Critical set S_290          <->  Minimal race-budget set
                                       certifying universality
    * Bhargava-Hanke implication  <->  Limit closure beyond
                                       finite race-budget
    * Lagrange industrial bound   <->  Race-budget at production
                                       scale (n <= 1000)

  Sources
  -------
    * J.-L. Lagrange. "Demonstration d'un theoreme d'arithmetique".
      Nouv. Mem. Acad. Roy. Sci. Berlin (1770) 123-133.
    * J. H. Conway and W. A. Schneeberger. Unpublished proof of the
      15-theorem (1993). See M. Bhargava, "On the Conway-
      Schneeberger fifteen theorem", Contemp. Math. 272 (2000) 27.
    * M. Bhargava and J. Hanke. "Universal quadratic forms and the
      290-theorem". Preprint, 2005-2011.

  No imports beyond `Init`. No axioms, no `sorry`.
-/

namespace UniversalQuadraticForms290

-- ══════════════════════════════════════════════════════════
-- PART 1: SQUARE AND BOUNDED INTEGER-SQUARE-ROOT
-- ══════════════════════════════════════════════════════════

/-- Square of a natural number. -/
def sq (n : Nat) : Nat := n * n

/-- Bounded integer square root: largest k with k*k <= n, computed by
    linear search up to a fuel bound. For our use case the fuel is
    n + 1 so the bound is reached. -/
def isqrt (n : Nat) : Nat :=
  let rec go (k : Nat) (fuel : Nat) : Nat :=
    match fuel with
    | 0     => k
    | f + 1 => if (k + 1) * (k + 1) <= n then go (k + 1) f else k
  go 0 n

theorem isqrt_0  : isqrt 0  = 0  := by native_decide
theorem isqrt_1  : isqrt 1  = 1  := by native_decide
theorem isqrt_4  : isqrt 4  = 2  := by native_decide
theorem isqrt_15 : isqrt 15 = 3  := by native_decide
theorem isqrt_290 : isqrt 290 = 17 := by native_decide

-- ══════════════════════════════════════════════════════════
-- PART 2: FOUR-SQUARE WITNESS SEARCH
-- ══════════════════════════════════════════════════════════
-- We search for (a, b, c, d) with a^2 + b^2 + c^2 + d^2 = n by
-- iterating a from isqrt(n) down to 0, then for each a iterating
-- b similarly on the remainder, and so on. The search returns the
-- first (lexicographically) witness found, as an Option.

/-- Two-square witness for `n`: returns `some (c, d)` with
    c^2 + d^2 = n if found. -/
def findTwoSquares (n : Nat) : Option (Nat × Nat) :=
  let rec go (c : Nat) (fuel : Nat) : Option (Nat × Nat) :=
    match fuel with
    | 0     => none
    | f + 1 =>
      let cc := c * c
      if cc > n then none
      else
        let r := n - cc
        let d := isqrt r
        if d * d == r then some (c, d) else go (c + 1) f
  go 0 (n + 1)

/-- Three-square witness for `n`: returns `some (b, c, d)` with
    b^2 + c^2 + d^2 = n if found. -/
def findThreeSquares (n : Nat) : Option (Nat × Nat × Nat) :=
  let rec go (b : Nat) (fuel : Nat) : Option (Nat × Nat × Nat) :=
    match fuel with
    | 0     => none
    | f + 1 =>
      let bb := b * b
      if bb > n then none
      else
        match findTwoSquares (n - bb) with
        | some (c, d) => some (b, c, d)
        | none        => go (b + 1) f
  go 0 (n + 1)

/-- Four-square witness for `n`: returns `some (a, b, c, d)` with
    a^2 + b^2 + c^2 + d^2 = n if found. By Lagrange's theorem this
    is `some` for every natural n; the search exhibits the witness. -/
def findFourSquares (n : Nat) : Option (Nat × Nat × Nat × Nat) :=
  let rec go (a : Nat) (fuel : Nat) : Option (Nat × Nat × Nat × Nat) :=
    match fuel with
    | 0     => none
    | f + 1 =>
      let aa := a * a
      if aa > n then none
      else
        match findThreeSquares (n - aa) with
        | some (b, c, d) => some (a, b, c, d)
        | none           => go (a + 1) f
  go 0 (n + 1)

/-- Predicate: the four-square representation exists and verifies. -/
def fourSquaresWorks (n : Nat) : Bool :=
  match findFourSquares n with
  | some (a, b, c, d) => a*a + b*b + c*c + d*d == n
  | none              => false

-- A few literal sanity checks at the smallest scales.
theorem fourSquares_1   : fourSquaresWorks 1   = true := by native_decide
theorem fourSquares_2   : fourSquaresWorks 2   = true := by native_decide
theorem fourSquares_7   : fourSquaresWorks 7   = true := by native_decide
theorem fourSquares_15  : fourSquaresWorks 15  = true := by native_decide
theorem fourSquares_23  : fourSquaresWorks 23  = true := by native_decide
theorem fourSquares_290 : fourSquaresWorks 290 = true := by native_decide

-- ══════════════════════════════════════════════════════════
-- PART 3: BOUNDED RANGE HELPER
-- ══════════════════════════════════════════════════════════

/-- The ascending integer range [1..n]. -/
def asc (n : Nat) : List Nat :=
  let rec go (i : Nat) (acc : List Nat) : List Nat :=
    match i with
    | 0     => acc
    | k + 1 => go k ((k + 1) :: acc)
  go n []

theorem asc_5 : asc 5 = [1, 2, 3, 4, 5] := by native_decide
theorem asc_15 : asc 15 = [1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] := by native_decide

-- ══════════════════════════════════════════════════════════
-- PART 4: LAGRANGE FOUR-SQUARE THEOREM AT SCALE 290
-- ══════════════════════════════════════════════════════════
-- Every positive integer n in [1, 290] is the sum of four squares.
-- Verified by `native_decide` over the explicit list.

/-- Lagrange's four-square theorem at scale 290: every n in [1, 290]
    has an explicit (a, b, c, d) with a^2 + b^2 + c^2 + d^2 = n. -/
theorem lagrange_four_square_to_290 :
    (asc 290).all fourSquaresWorks = true := by native_decide

-- ══════════════════════════════════════════════════════════
-- PART 5: CONWAY-SCHNEEBERGER 15-THEOREM SHADOW
-- ══════════════════════════════════════════════════════════
-- The 15-theorem critical set:
--     T_15 = {1, 2, 3, 5, 6, 7, 10, 14, 15}
-- The four-square form x^2+y^2+z^2+w^2 (which has integer matrix)
-- represents each of these. Plus we verify representation of every
-- n in [1, 15] for completeness.

/-- The Conway-Schneeberger 15-theorem critical numbers (refined
    list as in Bhargava 2000). -/
def criticalSet15 : List Nat := [1, 2, 3, 5, 6, 7, 10, 14, 15]

/-- The four-square form represents every member of the
    Conway-Schneeberger critical set. -/
theorem four_square_represents_critical_15 :
    criticalSet15.all fourSquaresWorks = true := by native_decide

/-- The four-square form represents every n in [1, 15]. -/
theorem four_square_represents_to_15 :
    (asc 15).all fourSquaresWorks = true := by native_decide

/-- Conway-Schneeberger witness: the four-square form represents
    every member of the 15 critical set. By the Conway-Schneeberger
    theorem (the "if it represents 1..15 then it represents all"
    direction, NOT mechanized), the form is universal. -/
theorem conway_schneeberger_15 :
    criticalSet15.all fourSquaresWorks = true := by native_decide

-- ══════════════════════════════════════════════════════════
-- PART 6: BHARGAVA-HANKE 290-THEOREM SHADOW
-- ══════════════════════════════════════════════════════════
-- The 290-theorem's 29 critical numbers:

/-- The Bhargava-Hanke 290-theorem critical set (29 numbers). -/
def criticalSet290 : List Nat :=
  [1, 2, 3, 5, 6, 7, 10, 13, 14, 15, 17, 19, 21, 22, 23, 26, 29,
   30, 31, 34, 35, 37, 42, 58, 93, 110, 145, 203, 290]

/-- The 290 critical set has the announced cardinality. -/
theorem criticalSet290_card : criticalSet290.length = 29 := by native_decide

/-- The four-square form represents every member of the
    Bhargava-Hanke critical set. -/
theorem four_square_represents_critical_290 :
    criticalSet290.all fourSquaresWorks = true := by native_decide

/-- The Bhargava-Hanke witness: the four-square form represents every
    one of the 29 critical numbers. By the Bhargava-Hanke 290-theorem
    (the "if it represents S_290 then it represents all positive
    integers" direction, NOT mechanized), the form is universal. -/
theorem bhargava_hanke_witness :
    criticalSet290.all fourSquaresWorks = true := by native_decide

-- ══════════════════════════════════════════════════════════
-- PART 7: CONCRETE WITNESS DISPLAYS
-- ══════════════════════════════════════════════════════════
-- A few explicit decompositions to anchor the verification: each
-- of the most subtle critical numbers shown by hand.

/-- 7 = 2^2 + 1^2 + 1^2 + 1^2 (one of two essentially different
    representations of 7 as a sum of four squares; the other is
    2^2 + 1^2 + 1^2 + 1^2 with a different ordering). -/
theorem seven_decomp : 2*2 + 1*1 + 1*1 + 1*1 = 7 := by native_decide

/-- 15 = 3^2 + 2^2 + 1^2 + 1^2. -/
theorem fifteen_decomp : 3*3 + 2*2 + 1*1 + 1*1 = 15 := by native_decide

/-- 23 = 3^2 + 3^2 + 2^2 + 1^2. -/
theorem twentythree_decomp : 3*3 + 3*3 + 2*2 + 1*1 = 23 := by native_decide

/-- 290 = 16^2 + 5^2 + 3^2 + 0^2 = 256 + 25 + 9 + 0. (The
    `findFourSquares` search may pick a different representative;
    this is one valid decomposition.) -/
theorem twoninety_decomp : 16*16 + 5*5 + 3*3 + 0*0 = 290 := by native_decide

-- ══════════════════════════════════════════════════════════
-- PART 8: LAGRANGE AT INDUSTRIAL SCALE (BONUS)
-- ══════════════════════════════════════════════════════════
-- Stretch the Lagrange witness to n in [1, 1000]. This is the
-- production-scale shadow of "every positive integer is a sum of
-- four squares". Compute cost is ~1000 * O(n) ~ a million tape
-- ops, well within `native_decide`'s budget.

/-- Lagrange's four-square theorem at industrial scale 1000. -/
theorem lagrange_four_square_to_1000 :
    (asc 1000).all fourSquaresWorks = true := by native_decide

-- ══════════════════════════════════════════════════════════
-- PART 9: STRUCTURAL SUMMARY
-- ══════════════════════════════════════════════════════════

/-- The full mechanized record: Lagrange at scale 1000 plus the
    Conway-Schneeberger and Bhargava-Hanke critical-set witnesses. -/
theorem universal_quadratic_form_record :
    (asc 1000).all fourSquaresWorks = true
  ∧ criticalSet15.all fourSquaresWorks = true
  ∧ criticalSet290.all fourSquaresWorks = true
  ∧ criticalSet290.length = 29 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide

-- ══════════════════════════════════════════════════════════
-- PART 10: THE WALLS, NAMED EXPLICITLY
-- ══════════════════════════════════════════════════════════
-- We distinguish two walls in this file:
--
--   (W1) DEEP WALL --- THE BHARGAVA-HANKE IMPLICATION.
--        The full 290-theorem says:
--           if a positive-definite integer-matrix quadratic form Q
--           represents every n in S_290, then Q represents every
--           positive integer.
--        The proof requires escalator-form classification (Bhargava
--        2000), explicit lattice geometry, and Siegel-mass
--        estimates over a 6436-element family of escalator forms.
--        It is not a finitary check on a single quadratic form ---
--        it is a structural theorem about the entire class of such
--        forms. Outside `native_decide` and outside the
--        country-church chapel.
--
--   (W2) DEEP WALL --- THE CONWAY-SCHNEEBERGER IMPLICATION.
--        The 15-theorem (Conway-Schneeberger 1993, formalized by
--        Bhargava 2000) says:
--           if Q has integer matrix and represents 1..15 (with the
--           refinement to T_15), Q represents every positive
--           integer.
--        Same structural character as W1; deferred for the same
--        reason.
--
-- What we DO mechanize: the WITNESS direction --- exhibit explicit
-- four-square decompositions for every member of the critical sets
-- (and for every n in [1, 1000] as the industrial bonus). The
-- existence of these witnesses is what makes the four-square form
-- a candidate for universality; the IMPLICATION that establishes
-- universality is the deep theorem.

/-- The unproven Bhargava-Hanke implication, named as a `Prop` so
    that future work has an explicit target to chase. We do NOT
    prove it; doing so requires the full 2005 paper. -/
def bhargava_hanke_implication_unproven : Prop :=
  ∀ Q : Nat → Nat → Nat → Nat → Nat,  -- a 4-variable form Q(a,b,c,d)
    (∀ n ∈ criticalSet290, ∃ a b c d : Nat, Q a b c d = n) →
    (∀ n : Nat, n ≥ 1 → ∃ a b c d : Nat, Q a b c d = n)

-- ══════════════════════════════════════════════════════════
-- HISTORY OF ATTEMPTS (for future agents)
-- ══════════════════════════════════════════════════════════
-- First draft tried a naive O(N^4) search on (a, b, c, d) all
-- iterating from 0 to floor(sqrt N). For N = 290 this is
-- 18^4 = ~105K per number * 290 numbers = ~30M iterations.
-- `native_decide` finished but slowly. Switched to the layered
-- isqrt-based search (PART 2) which is O(N) per number; the full
-- N = 1000 list now finishes in seconds.
--
-- Considered shipping a separate verifier for each of x^2+y^2+z^2,
-- x^2+y^2+2z^2, x^2+y^2+z^2+2w^2 etc. (the full Bhargava-Hanke
-- escalator family). Each is structurally identical to the
-- four-square verifier; they buy nothing the four-square version
-- does not already exhibit. Deferred to follow-on work if the
-- chapel grows.
--
-- The criticalSet290 list was checked against Bhargava-Hanke 2005,
-- Theorem 1 (the 29 critical numbers). The criticalSet15 list
-- follows the refinement in Bhargava 2000, "On the Conway-
-- Schneeberger fifteen theorem", Section 2.
--
-- Decision: ship the witness side of both 15- and 290-theorems
-- (mechanized at scale), document the deep implications as the
-- explicit walls, and stretch Lagrange to N = 1000 as the
-- industrial bonus. This is the honest country-church accounting
-- for the universal quadratic forms program.

end UniversalQuadraticForms290
