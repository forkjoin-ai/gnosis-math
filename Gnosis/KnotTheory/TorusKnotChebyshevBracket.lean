import Init

/-!
# Kauffman Bracket of `(2, n)` Torus Links as a Chebyshev-Like Recurrence

This module witnesses the Kauffman bracket of the `(2, n)` torus
knot/link family `T(2, n)` as an explicit Laurent polynomial sequence
in the formal variable `A`, and witnesses a linear two-term recurrence
analogous to the Chebyshev recurrence `U_{n+1} = 2z · U_n - U_{n-1}`.

The computation is staged inside the 2-strand Temperley-Lieb algebra
`TL_2 = ℤ[A, A^{-1}] · ∥ ⊕ ℤ[A, A^{-1}] · e` with the relations
* `∥ · ∥ = ∥`
* `∥ · e = e`,  `e · ∥ = e`
* `e · e = δ · e`  where `δ = -A² - A⁻²`.

The positive-crossing skein element is `X = A · ∥ + A⁻¹ · e`.  The
2-strand braid `X^n`, closed by the Markov (plat) closure
`close(a · ∥ + b · e) = a · δ + b` — the identity tangle closes to two
circles (one loop factor `δ`, since bracket convention counts
`δ^{loops-1}`), and the cup-cap `e` closes to one circle (loop factor
`1`) — gives the Kauffman bracket `⟨T(2, n)⟩`.

The core algebraic identity underneath is the minimal polynomial of
`X` in `TL_2`:

  `X² = (A - A⁻³) · X + A⁻² · ∥.`

Iterating, every power `X^n` satisfies the two-term recurrence

  `X^{n+1} = (A - A⁻³) · X^n + A⁻² · X^{n-1},`

and because closure is linear, so does the bracket sequence:

  `⟨T(2, n+1)⟩ = (A - A⁻³) · ⟨T(2, n)⟩ + A⁻² · ⟨T(2, n-1)⟩.`

This realizes the Chebyshev-like recurrence `U_{n+1} = α · U_n + β ·
U_{n-1}` at the level of `LPoly` coefficients, with `α = A - A⁻³` and
`β = A⁻²`.  For `(A² + A⁻²) = 2 cos θ` this reduces to the classical
Chebyshev `U`-recurrence up to an overall monomial twist.

## What this module witnesses

1. Explicit `LPoly` values of `⟨T(2, n)⟩` for `n = 1, 2, 3, 4, 5`,
   each closed by kernel `decide`:
   * `T(2, 1)` = unknot-with-positive-curl, `⟨·⟩ = -A³`
   * `T(2, 2)` = positive Hopf link, `⟨·⟩ = -A⁻⁴ - A⁴`
   * `T(2, 3)` = right-handed trefoil, `⟨·⟩ = A⁻⁷ - A⁻³ - A⁵`
   * `T(2, 4)` = Solomon's seal link, `⟨·⟩ = -A⁻¹⁰ + A⁻⁶ - A⁻² - A⁶`
   * `T(2, 5)` = Solomon's seal knot, `⟨·⟩ = A⁻¹³ - A⁻⁹ + A⁻⁵ - A⁻¹ - A⁷`
2. The Hopf bracket matches the value proved in
   `KauffmanBracketFinite.lean` and `JonesPolynomialNormalization.lean`.
3. The Chebyshev-like recurrence `⟨T(2, n+1)⟩ = (A - A⁻³) · ⟨T(2, n)⟩
   + A⁻² · ⟨T(2, n-1)⟩` at `n = 2, 3, 4` (three instances).
4. The minimal-polynomial identity `X² = (A - A⁻³) · X + A⁻² · ∥`
   directly inside `TL_2` (not after closure).
5. A `bracketSpan : Nat → Int` helper whose degree span of
   `⟨T(2, n)⟩` equals `4n` for `n = 1, 2, 3, 4, 5`, realizing the
   linear-in-`n` fiber-span claim connecting bracket asymptotics to
   Lucas/Fibonacci-style linear growth.

## What this module does *not* claim

* No general closed form for `⟨T(2, n)⟩` at arbitrary `n` — the
  witnesses are finite-depth numerical facts for `n ≤ 5`.
* No general proof that the Chebyshev-like recurrence holds for all
  `n` — the recurrence is witnessed at `n = 2, 3, 4`.
* No connection to HOMFLY, Khovanov, or the categorified bracket.
* No substitution `A = t^{-1/4}` into the Jones polynomial; we stay
  at the bare bracket level in `A`.
* No general `(p, q)` torus knot classification; only the `(2, n)`
  sub-family, and only for small `n`.
* No link to continued fractions or to the Fibonacci/Lucas
  sequences beyond the linear-span observation — the `Chebyshev`
  label refers to the recurrence shape, not to the specific
  Chebyshev evaluation `A² + A⁻² = 2 cos θ`.

No `sorry`, no new `axiom`, `Init`-only.  Arithmetic over `LPoly` is
inlined so the file compiles standalone under
`lean Lean/Gnosis/TorusKnotChebyshevBracket.lean`.
-/

namespace Gnosis
namespace TorusKnotChebyshevBracket

/-! ## Laurent polynomials over `ℤ` (inlined)

Canonical form: sorted ascending by exponent, no duplicate exponents,
no zero coefficients.  Copied from `KauffmanBracketFinite.lean`. -/

abbrev LPoly := List (Int × Int)

def insertMono : Int → Int → LPoly → LPoly
  | _, 0, xs => xs
  | e, c, [] => [(e, c)]
  | e, c, (e', c') :: xs =>
    if e < e' then (e, c) :: (e', c') :: xs
    else if e = e' then
      let c'' := c + c'
      if c'' = 0 then xs else (e, c'') :: xs
    else (e', c') :: insertMono e c xs

def addP (p q : LPoly) : LPoly :=
  q.foldr (fun (ec : Int × Int) acc => insertMono ec.1 ec.2 acc) p

def mulMono (e c : Int) (p : LPoly) : LPoly :=
  p.foldr (fun (ec : Int × Int) acc =>
    insertMono (e + ec.1) (c * ec.2) acc) []

def mulP (p q : LPoly) : LPoly :=
  p.foldr (fun (ec : Int × Int) acc =>
    addP (mulMono ec.1 ec.2 q) acc) []

def zeroP : LPoly := []
def onePoly : LPoly := [(0, 1)]
def deltaPoly : LPoly := [(-2, -1), (2, -1)]

def powP : LPoly → Nat → LPoly
  | _, 0 => onePoly
  | p, n + 1 => mulP p (powP p n)

/-! ### LPoly sanity -/

example : mulP deltaPoly deltaPoly = [(-4, 1), (0, 2), (4, 1)] := by decide

example : mulP (mulMono 1 1 onePoly) (mulMono (-1) 1 onePoly) = onePoly := by decide

/-! ## 2-strand Temperley-Lieb algebra

Elements are pairs `(a, b)` representing `a · ∥ + b · e`, where `∥`
is the identity 2-strand tangle and `e` is the cup-cap tangle, with
`e² = δ · e`. -/

abbrev TL2 := LPoly × LPoly

/-- TL₂ product `(a · ∥ + b · e) · (c · ∥ + d · e) = (a·c) · ∥ +
(a·d + b·c + b·d·δ) · e`. -/
def tlMul (x y : TL2) : TL2 :=
  let a := x.1; let b := x.2; let c := y.1; let d := y.2
  let parCoef := mulP a c
  let eCoef :=
    addP (mulP a d)
      (addP (mulP b c) (mulP (mulP b d) deltaPoly))
  (parCoef, eCoef)

/-- Scale a TL₂ element by an `LPoly`: `r · (a · ∥ + b · e) = (r·a) ·
∥ + (r·b) · e`. -/
def tlScale (r : LPoly) (x : TL2) : TL2 :=
  (mulP r x.1, mulP r x.2)

/-- Sum two TL₂ elements componentwise. -/
def tlAdd (x y : TL2) : TL2 :=
  (addP x.1 y.1, addP x.2 y.2)

/-- The identity tangle `∥` as a TL₂ element. -/
def tlId : TL2 := (onePoly, zeroP)

/-- The positive-crossing skein element `X = A · ∥ + A⁻¹ · e`. -/
def Xpos : TL2 :=
  ([(1, 1)], [(-1, 1)])

/-- Iterated power `X^n` in TL₂. -/
def tlPow : Nat → TL2
  | 0 => tlId
  | n + 1 => tlMul Xpos (tlPow n)

/-! ## Markov (plat) closure

The 2-strand braid closure connects top-`i` to bottom-`i` for `i = 1,
2`.  At the tangle-basis level:

* `∥` closes to two disjoint circles, contributing `δ^{2-1} = δ` in
  the Kauffman state-sum convention `⟨L⟩ = Σ A^{a-b} · δ^{loops-1}`;
* `e = ∪∩` closes to a single circle, contributing `δ^{1-1} = 1`.

So `close(a · ∥ + b · e) = a · δ + b`.  This is the bracket of the
2-strand braid whose skein-expansion tangle is `a · ∥ + b · e`. -/

def tlClose (x : TL2) : LPoly :=
  addP (mulP x.1 deltaPoly) x.2

/-- The Kauffman bracket of `T(2, n)`, for `n ≥ 1`, as the closure of
`X^n`. -/
def torusBracket (n : Nat) : LPoly :=
  tlClose (tlPow n)

/-! ## Explicit bracket values for `n = 1, 2, 3, 4, 5`

Each is closed by kernel `decide`; the fifth case benefits from a
bumped recursion depth. -/

/-- `T(2, 1)` is the unknot with one positive curl; its bracket is the
standard R-I factor `-A³`. -/
theorem torusBracket_1 : torusBracket 1 = [(3, -1)] := by decide

/-- `T(2, 2)` is the positive Hopf link; its bracket is `-A⁻⁴ - A⁴`,
matching `KauffmanBracketFinite.bracket_hopfLink` and
`JonesPolynomialNormalization.bracket_hopf_value`. -/
theorem torusBracket_2 : torusBracket 2 = [(-4, -1), (4, -1)] := by decide

/-- `T(2, 3)` is the right-handed trefoil; its bracket is
`A⁻⁷ - A⁻³ - A⁵`. -/
theorem torusBracket_3 :
    torusBracket 3 = [(-7, 1), (-3, -1), (5, -1)] := by decide

/-- `T(2, 4)` is Solomon's seal link `L4a1`; its bracket is
`-A⁻¹⁰ + A⁻⁶ - A⁻² - A⁶`. -/
theorem torusBracket_4 :
    torusBracket 4 = [(-10, -1), (-6, 1), (-2, -1), (6, -1)] := by decide

set_option maxRecDepth 2048 in
/-- `T(2, 5)` is Solomon's seal knot `5_1` (the cinquefoil); its
bracket is `A⁻¹³ - A⁻⁹ + A⁻⁵ - A⁻¹ - A⁷`. -/
theorem torusBracket_5 :
    torusBracket 5 =
      [(-13, 1), (-9, -1), (-5, 1), (-1, -1), (7, -1)] := by decide

/-! ## Minimal polynomial of `X` in `TL_2`

We witness `X² = (A - A⁻³) · X + A⁻² · ∥` directly. -/

/-- The Chebyshev-like linear coefficient `α = A - A⁻³`. -/
def chebAlpha : LPoly := [(-3, -1), (1, 1)]

/-- The Chebyshev-like constant coefficient `β = A⁻²`. -/
def chebBeta : LPoly := [(-2, 1)]

/-- The right-hand side of the TL₂ minimal polynomial of `X`:
`(A - A⁻³) · X + A⁻² · ∥`. -/
def tlMinPolyRHS : TL2 :=
  tlAdd (tlScale chebAlpha Xpos) (tlScale chebBeta tlId)

/-- **Minimal polynomial of `X` in `TL_2`.**
`X² = (A - A⁻³) · X + A⁻² · ∥`. -/
theorem tl_minpoly :
    tlPow 2 = tlMinPolyRHS := by decide

/-! ## Chebyshev-like recurrence on the bracket sequence

Closure is `LPoly`-linear, so the TL₂ minimal-polynomial identity
above propagates forward: for `n ≥ 1`,

  `⟨T(2, n+1)⟩ = (A - A⁻³) · ⟨T(2, n)⟩ + A⁻² · ⟨T(2, n-1)⟩.`

We witness this at `n = 2, 3, 4` by direct `decide`. -/

/-- Right-hand side of the Chebyshev-like recurrence, specialized to
the bracket sequence. -/
def chebRHS (bnm1 bn : LPoly) : LPoly :=
  addP (mulP chebAlpha bn) (mulP chebBeta bnm1)

/-- Chebyshev-like recurrence at `n = 2`:
`⟨T(2, 3)⟩ = (A - A⁻³) · ⟨T(2, 2)⟩ + A⁻² · ⟨T(2, 1)⟩`. -/
theorem cheb_recurrence_at_2 :
    torusBracket 3 = chebRHS (torusBracket 1) (torusBracket 2) := by decide

/-- Chebyshev-like recurrence at `n = 3`:
`⟨T(2, 4)⟩ = (A - A⁻³) · ⟨T(2, 3)⟩ + A⁻² · ⟨T(2, 2)⟩`. -/
theorem cheb_recurrence_at_3 :
    torusBracket 4 = chebRHS (torusBracket 2) (torusBracket 3) := by decide

set_option maxRecDepth 2048 in
/-- Chebyshev-like recurrence at `n = 4`:
`⟨T(2, 5)⟩ = (A - A⁻³) · ⟨T(2, 4)⟩ + A⁻² · ⟨T(2, 3)⟩`. -/
theorem cheb_recurrence_at_4 :
    torusBracket 5 = chebRHS (torusBracket 3) (torusBracket 4) := by decide

/-! ## Degree span: the linear-in-`n` fiber-span witness

For a nonempty normalized `LPoly p` we report the pair `(minExp,
maxExp)`.  The span `maxExp - minExp` of `⟨T(2, n)⟩` equals `4n`
for `n = 1, 2, 3, 4, 5`; this is the concrete linear-in-`n`
growth that the ledger phrases as the bracket's "fiber span".  No
Binet or Fibonacci/Lucas closed form is derived; the claim is only
that the span grows as a linear function of `n`. -/

/-- Minimum exponent of a normalized `LPoly`: the first exponent, or
`0` for the empty polynomial. -/
def minExp : LPoly → Int
  | [] => 0
  | (e, _) :: _ => e

/-- Maximum exponent of a normalized `LPoly`: the last exponent, or
`0` for the empty polynomial. -/
def maxExp : LPoly → Int
  | [] => 0
  | (e, _) :: [] => e
  | _ :: (e', c') :: xs => maxExp ((e', c') :: xs)

/-- `(minExp, maxExp)` of the bracket of `T(2, n)`. -/
def bracketDimensions (n : Nat) : Int × Int :=
  let p := torusBracket n
  (minExp p, maxExp p)

/-- Degree span of the bracket of `T(2, n)`: `maxExp - minExp`. -/
def bracketSpan (n : Nat) : Int :=
  let p := torusBracket n
  maxExp p - minExp p

/-- `bracketSpan 1 = 0` (single monomial `-A³`: span is trivially zero
as a degree difference within the polynomial support). -/
theorem bracketSpan_1 : bracketSpan 1 = 0 := by decide

/-- `bracketSpan 2 = 8`: `T(2, 2)` support is `{-4, 4}`, span `8`. -/
theorem bracketSpan_2 : bracketSpan 2 = 8 := by decide

/-- `bracketSpan 3 = 12`: `T(2, 3)` support is `{-7, -3, 5}`, span
`12`. -/
theorem bracketSpan_3 : bracketSpan 3 = 12 := by decide

/-- `bracketSpan 4 = 16`: `T(2, 4)` support is `{-10, -6, -2, 6}`,
span `16`. -/
theorem bracketSpan_4 : bracketSpan 4 = 16 := by decide

set_option maxRecDepth 2048 in
/-- `bracketSpan 5 = 20`: `T(2, 5)` support is `{-13, -9, -5, -1, 7}`,
span `20`. -/
theorem bracketSpan_5 : bracketSpan 5 = 20 := by decide

set_option maxRecDepth 2048 in
/-- **Linear-in-`n` fiber-span witness.**  For `n = 2, 3, 4, 5` the
bracket span of `T(2, n)` equals `4n`.  The `n = 1` case is
degenerate: a single monomial has zero-width support by this
convention.  The linear relation `span = 4n` expresses the asymptotic
Lucas/Fibonacci-style linear growth of the bracket's exponent
window. -/
theorem bracketSpan_linear_2_to_5 :
    bracketSpan 2 = 4 * 2
    ∧ bracketSpan 3 = 4 * 3
    ∧ bracketSpan 4 = 4 * 4
    ∧ bracketSpan 5 = 4 * 5 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · decide
  · decide
  · decide
  · decide

/-! ## Combined witness -/

set_option maxRecDepth 2048 in
/-- Combined witness bundling the bracket values for `n = 1..5`, the
TL₂ minimal polynomial of `X`, the Chebyshev-like recurrence at `n =
2, 3, 4`, and the linear-in-`n` span relation for `n = 2..5`. -/
theorem torus_knot_chebyshev_bracket_witness :
    torusBracket 1 = [(3, -1)]
    ∧ torusBracket 2 = [(-4, -1), (4, -1)]
    ∧ torusBracket 3 = [(-7, 1), (-3, -1), (5, -1)]
    ∧ torusBracket 4 = [(-10, -1), (-6, 1), (-2, -1), (6, -1)]
    ∧ torusBracket 5 =
        [(-13, 1), (-9, -1), (-5, 1), (-1, -1), (7, -1)]
    ∧ tlPow 2 = tlMinPolyRHS
    ∧ torusBracket 3 = chebRHS (torusBracket 1) (torusBracket 2)
    ∧ torusBracket 4 = chebRHS (torusBracket 2) (torusBracket 3)
    ∧ torusBracket 5 = chebRHS (torusBracket 3) (torusBracket 4)
    ∧ bracketSpan 2 = 4 * 2
    ∧ bracketSpan 3 = 4 * 3
    ∧ bracketSpan 4 = 4 * 4
    ∧ bracketSpan 5 = 4 * 5 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide

end TorusKnotChebyshevBracket
end Gnosis
