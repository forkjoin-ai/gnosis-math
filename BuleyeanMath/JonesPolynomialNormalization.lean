import Init

/-!
# Jones Polynomial via Writhe Normalization of the Kauffman Bracket

This module witnesses the passage from the Kauffman bracket `⟨L⟩` to
the (unevaluated) Jones polynomial via the writhe normalization

  `X(L) := (-A)^(-3 · w(L)) · ⟨L⟩`

where `w(L)` is the writhe (sum of crossing signs) of an oriented
link diagram `L`. We keep everything as a Laurent polynomial in the
formal variable `A`; the usual substitution `A = t^{-1/4}` that
turns `X(L)` into `V(L)(t)` is not performed here, to avoid
fractional exponents.

Content is `import Init` only, no `sorry`, no new `axiom`. The
`LPoly` arithmetic is inlined (copied from
`KauffmanBracketFinite.lean` / `FoldedKnotIsomorphism.lean`) so the
file compiles standalone under
`lean Lean/BuleyeanMath/JonesPolynomialNormalization.lean`.

What this module witnesses:

* explicit values of the normalized bracket `X(L)` on the unknot, on
  the positive Hopf link (two positive crossings), on the negative
  Hopf link (two negative crossings), and on a one-crossing "unknot
  with a positive curl" diagram;
* the normalized-bracket distinction between the positive and the
  negative Hopf link — the bare Kauffman bracket cannot tell them
  apart, but the writhe-corrected normalization does;
* one explicit Reidemeister-I witness: the normalized bracket of a
  diagram agrees with the normalized bracket of the same diagram
  with one added positive curl, with the writhe correction cancelling
  the `-A^3` factor that the bare bracket picks up under R-I.

What this module does *not* claim:

* no general theorem that `X` is an invariant of oriented links —
  Reidemeister invariance is verified only on one explicit instance
  for R-I;
* no claim that the Jones polynomial is a complete invariant of
  oriented links (it is not);
* the chosen `loops` functions are hard-coded for the listed
  diagrams only.
-/

namespace BuleyeanMath
namespace JonesPolynomialNormalization

/-! ## Laurent polynomials over ℤ (inlined from `KauffmanBracketFinite`)

Canonical form: sorted ascending by exponent, no duplicate exponents,
no zero coefficients. -/

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

def onePoly : LPoly := [(0, 1)]
def deltaPoly : LPoly := [(-2, -1), (2, -1)]

def powP : LPoly → Nat → LPoly
  | _, 0 => onePoly
  | p, n+1 => mulP p (powP p n)

/-! ## State-sum Kauffman bracket (inlined) -/

def allStates : Nat → List (List Bool)
  | 0     => [[]]
  | k + 1 =>
    let tails := allStates k
    tails.map (true :: ·) ++ tails.map (false :: ·)

def aMinusBOf : List Bool → Int
  | []            => 0
  | true  :: xs   => 1  + aMinusBOf xs
  | false :: xs   => -1 + aMinusBOf xs

def deltaPow (loops : Nat) : LPoly :=
  match loops with
  | 0     => onePoly
  | k + 1 => powP deltaPoly k

def bracketSum (n : Nat) (loops : List Bool → Nat) : LPoly :=
  (allStates n).foldr
    (fun s acc => addP (mulMono (aMinusBOf s) 1 (deltaPow (loops s))) acc)
    []

/-! ## Oriented crossings and the writhe

A signed crossing carries an index and a Boolean sign, where `true`
means a positive crossing (`+1` contribution to the writhe) and
`false` means a negative crossing (`-1`). -/

structure Crossing where
  idx  : Nat
  sign : Bool
deriving DecidableEq, Repr

/-- Writhe of a list of signed crossings: sum of `+1` for positive
crossings and `-1` for negative crossings. -/
def writhe : List Crossing → Int
  | []        => 0
  | c :: cs   => (if c.sign then (1 : Int) else -1) + writhe cs

/-! ## The monomial `(-A)^n` as a Laurent polynomial

`(-A)^n = (-1)^n · A^n`. As an `LPoly` this is the single-term list
`[(n, (-1)^n)]`, valid for both positive and negative `n`. The sign
`(-1)^n` depends only on the parity of `n`, which we read off with
`Int.emod n 2`. -/

/-- `(-1)^n` for `n : Int`, computed via parity. -/
def negOnePow (n : Int) : Int :=
  if n % 2 = 0 then 1 else -1

/-- `(-A)^n` as an `LPoly`. -/
def negAPow (n : Int) : LPoly :=
  [(n, negOnePow n)]

/-! ## The normalized bracket `X(L) = (-A)^(-3 w(L)) · ⟨L⟩` -/

/-- Normalized bracket, in the form `(-A)^(-3 · writhe) · bracket`. -/
def normalizedBracket (w : Int) (bracket : LPoly) : LPoly :=
  mulP (negAPow (-3 * w)) bracket

/-! ## Explicit diagrams -/

/-- The unknot: zero crossings, trivially one loop. -/
def unknotCrossings : List Crossing := []

def unknotLoops : List Bool → Nat
  | [] => 1
  | _  => 0

def unknotBracket : LPoly := bracketSum 0 unknotLoops

/-- Positive Hopf link: two positive crossings. Writhe = +2. -/
def hopfPosCrossings : List Crossing :=
  [⟨0, true⟩, ⟨1, true⟩]

/-- Negative Hopf link: two negative crossings. Writhe = -2. -/
def hopfNegCrossings : List Crossing :=
  [⟨0, false⟩, ⟨1, false⟩]

/-- Hopf link loop function (orientation-independent at the bracket
level): both all-A and all-B smoothings give 2 components, mixed
smoothings give 1. -/
def hopfLoops : List Bool → Nat
  | [true, true]   => 2
  | [true, false]  => 1
  | [false, true]  => 1
  | [false, false] => 2
  | _              => 0

def hopfBracket : LPoly := bracketSum 2 hopfLoops

/-- The bare Kauffman bracket sees no difference between the two
orientations: `⟨Hopf+⟩ = ⟨Hopf-⟩ = -A^{-4} - A^4`. -/
theorem bracket_hopf_value :
    hopfBracket = [(-4, -1), (4, -1)] := by decide

/-! ## Writhe computations -/

theorem writhe_unknot : writhe unknotCrossings = 0 := by decide

theorem writhe_hopfPos : writhe hopfPosCrossings = 2 := by decide

theorem writhe_hopfNeg : writhe hopfNegCrossings = -2 := by decide

/-! ## Normalized bracket values

These are the (unevaluated) Jones-polynomial values in the variable
`A`. Substituting `A = t^{-1/4}` would give the standard Jones
polynomial `V(L)(t)`; we do not perform that substitution. -/

/-- `X(unknot) = 1`. -/
theorem normalizedBracket_unknot :
    normalizedBracket (writhe unknotCrossings) unknotBracket
      = [(0, 1)] := by decide

/-- `X(Hopf+) = -A^{-10} - A^{-2}`. -/
theorem normalizedBracket_hopfPos :
    normalizedBracket (writhe hopfPosCrossings) hopfBracket
      = [(-10, -1), (-2, -1)] := by decide

/-- `X(Hopf-) = -A^{2} - A^{10}`. -/
theorem normalizedBracket_hopfNeg :
    normalizedBracket (writhe hopfNegCrossings) hopfBracket
      = [(2, -1), (10, -1)] := by decide

/-- The normalized bracket distinguishes the positive Hopf link from
the negative Hopf link, even though the bare Kauffman bracket
cannot. -/
theorem hopfPos_ne_hopfNeg_normalized :
    normalizedBracket (writhe hopfPosCrossings) hopfBracket
      ≠ normalizedBracket (writhe hopfNegCrossings) hopfBracket := by
  decide

/-! ## One Reidemeister-I witness

Let `D` be the empty (unknot) diagram: zero crossings, bracket `1`,
writhe `0`. Let `D'` be `D` with one added positive curl: one
positive crossing, bracket `-A^3 · ⟨D⟩ = -A^3`, writhe `+1`. The bare
bracket changes, but the writhe-normalized bracket `X` does not. -/

/-- Crossing list for "unknot with one positive curl". -/
def curlPosCrossings : List Crossing :=
  [⟨0, true⟩]

/-- Loop function for a single positive curl: the A-smoothing gives
two components (the curl encloses a small disk), the B-smoothing
gives one. The resulting bracket is `-A^3`, the exact R-I factor. -/
def curlPosLoops : List Bool → Nat
  | [true]  => 2
  | [false] => 1
  | _       => 0

def curlPosBracket : LPoly := bracketSum 1 curlPosLoops

/-- The bare bracket of the positive curl is `-A^3`, the standard
R-I factor. -/
theorem curlPosBracket_value :
    curlPosBracket = [(3, -1)] := by decide

/-- The writhe of the positive curl is `+1`. -/
theorem writhe_curlPos : writhe curlPosCrossings = 1 := by decide

/-- **Reidemeister-I witness.** The normalized bracket of the empty
diagram agrees with the normalized bracket of the same diagram with
one added positive curl: the writhe correction cancels the `-A^3`
factor that the bare Kauffman bracket picks up under R-I. -/
theorem normalizedBracket_R1_invariance_positive_curl :
    normalizedBracket (writhe unknotCrossings) unknotBracket
      = normalizedBracket (writhe curlPosCrossings) curlPosBracket := by
  decide

/-- Combined witness: writhe values agree with expectation, Kauffman
bracket does not distinguish the two Hopf orientations, and the
writhe-normalized bracket both distinguishes them *and* is invariant
under the chosen R-I move. -/
theorem jones_normalization_witness :
    writhe unknotCrossings = 0
    ∧ writhe hopfPosCrossings = 2
    ∧ writhe hopfNegCrossings = -2
    ∧ hopfBracket = [(-4, -1), (4, -1)]
    ∧ normalizedBracket (writhe unknotCrossings) unknotBracket
        = [(0, 1)]
    ∧ normalizedBracket (writhe hopfPosCrossings) hopfBracket
        = [(-10, -1), (-2, -1)]
    ∧ normalizedBracket (writhe hopfNegCrossings) hopfBracket
        = [(2, -1), (10, -1)]
    ∧ normalizedBracket (writhe hopfPosCrossings) hopfBracket
        ≠ normalizedBracket (writhe hopfNegCrossings) hopfBracket
    ∧ normalizedBracket (writhe unknotCrossings) unknotBracket
        = normalizedBracket (writhe curlPosCrossings) curlPosBracket := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide

end JonesPolynomialNormalization
end BuleyeanMath
