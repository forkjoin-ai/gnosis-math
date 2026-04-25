import Init

/-!
# Fermat-flavored Congruences on Kauffman Bracket Coefficients of `T(2, n)`

This module bridges three existing modules in
`Lean/BuleyeanMath/`:

* `JonesPolynomialNormalization.lean` (bracket, writhe, normalized
  bracket `X(L) = (-A)^(-3 w) · ⟨L⟩`),
* `TorusKnotChebyshevBracket.lean` (the `(2, n)` torus-link bracket
  sequence with Chebyshev-like two-term recurrence), and
* `FermatLittleInstances.lean` (`a^p ≡ a (mod p)` on small primes).

We reduce the coefficients of the Laurent polynomial `⟨T(2, n)⟩ ∈
ℤ[A, A⁻¹]` modulo small primes `p ∈ {3, 5, 7}` and report what
actually happens.  The module is deliberately empirical.  The name
"Fermat-flavored" refers to the *form* of the probes — reducing
coefficients mod `p`, collapsing exponents mod `p - 1` as if `A`
were a unit of `(ℤ/p)^×` where Fermat's little theorem forces
`A^{p-1} ≡ 1` — and not to any general identity on bracket
coefficients.

## Items witnessed

1. **Inlined `LPoly` arithmetic and the `T(2, n)` bracket** for
   `n = 1..5`, exactly matching
   `TorusKnotChebyshevBracket.torusBracket`.
2. **`coefAt : LPoly → Int → Int`** extracts the coefficient of
   `A^e` in canonical form.
3. **`bracketModP : LPoly → Nat → List (Int × Nat)`** reduces each
   coefficient modulo `p`, drops zero entries, and returns
   `(exponent, coefficient mod p)` pairs.
4. **Explicit `bracketModP` tables** for `T(2, n)`, `n = 2..5`, at
   `p = 3, 5, 7`, each closed by kernel `decide`.
5. **Fermat-flavored conjecture test (expected-negative).** We
   check whether the mod-`p` coefficient sequence, read off the
   exponents of `⟨T(2, n)⟩`, is periodic in the exponent with
   period `p - 1`.  It is not, generically — `A` is a formal
   Laurent variable, not an element of `(ℤ/p)^×` — and we report
   the negative observation honestly.
6. **Productive bridge: writhe mod `p - 1` on normalized brackets.**
   Positive Hopf has writhe `+2`, negative Hopf has writhe `-2`,
   differing by `4`.  If we *formally* collapse `A^4 = 1` on the
   normalized bracket (by reducing each exponent modulo `4`) and
   then reduce coefficients mod `5`, the two normalized brackets
   become equal.  This is exactly the "Fermat-style at a fourth
   root of unity" observation at `p = 5`.  Witnessed by `decide`.
7. **Torus-link Chebyshev period mod `p` (Pisano-like).**  For
   `p = 3, 5, 7` we reduce the bracket's coefficients mod `p` and
   collapse exponents mod `p - 1` (so the state lives in
   `(ℤ/p)^{p - 1}`).  Under the Chebyshev-like recurrence
   `b_{n+1} = (A - A⁻³) · b_n + A⁻² · b_{n-1}`, reduced the same
   way, we report empirical periods:

   * `p = 3`: period `2` (the sequence alternates two states),
   * `p = 5`: period `4`,
   * `p = 7`: period `2`.

   At `p = 3, 5` the period equals `p - 1`; at `p = 7` it does
   *not* — the period collapses to `2`.  This is the empirical
   surprise and the reason we report, not conjecture.

## Honest caveats

* Items 4, 5, 6, 7 are finite numerical witnesses closed by
  `decide`.  No general statement is made that bracket
  coefficients satisfy a Fermat-type congruence for all
  `(p, n)`; for most pairs they do not.
* The "formal `A^{p-1} = 1`" substitution used in items 6 and 7
  is not a valid algebra homomorphism from `ℤ[A, A⁻¹]` to any
  ring containing a primitive `(p-1)`-th root of unity over
  `ℤ/p`; it is a bookkeeping convenience that lets us see the
  writhe-shift cancellation as a discrete equality.
* The "period" in item 7 is the period of a particular folded
  state vector under the Chebyshev-like linear recurrence, read
  modulo `p`.  It is *not* the Pisano period of Fibonacci; the
  name is used loosely, for the analogous "period of a linear
  recurrence over `ℤ/p`".

No `sorry`, no new `axiom`, `Init`-only.  `LPoly` arithmetic and
the TL₂ machinery are inlined so the file compiles standalone:

  `cd lean && lean Lean/BuleyeanMath/JonesModPFermat.lean`.
-/

set_option maxRecDepth 4096

namespace BuleyeanMath
namespace JonesModPFermat

/-! ## Laurent polynomials over `ℤ` (inlined)

Canonical form: sorted ascending by exponent, no duplicate
exponents, no zero coefficients. -/

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

/-! ## 2-strand Temperley-Lieb algebra (inlined)

Matches `TorusKnotChebyshevBracket`: elements are pairs `(a, b)`
for `a · ∥ + b · e` with `e² = δ · e`. -/

abbrev TL2 := LPoly × LPoly

def tlMul (x y : TL2) : TL2 :=
  let a := x.1; let b := x.2; let c := y.1; let d := y.2
  let parCoef := mulP a c
  let eCoef :=
    addP (mulP a d)
      (addP (mulP b c) (mulP (mulP b d) deltaPoly))
  (parCoef, eCoef)

def tlId : TL2 := (onePoly, zeroP)

def Xpos : TL2 :=
  ([(1, 1)], [(-1, 1)])

def tlPow : Nat → TL2
  | 0 => tlId
  | n + 1 => tlMul Xpos (tlPow n)

def tlClose (x : TL2) : LPoly :=
  addP (mulP x.1 deltaPoly) x.2

/-- Kauffman bracket of `T(2, n)` for `n ≥ 1`, as the closure of
`X^n`.  Matches `TorusKnotChebyshevBracket.torusBracket`. -/
def torusBracket (n : Nat) : LPoly :=
  tlClose (tlPow n)

/-! ## Sanity: bracket values agree with `TorusKnotChebyshevBracket` -/

theorem torusBracket_1 : torusBracket 1 = [(3, -1)] := by decide

theorem torusBracket_2 : torusBracket 2 = [(-4, -1), (4, -1)] := by decide

theorem torusBracket_3 :
    torusBracket 3 = [(-7, 1), (-3, -1), (5, -1)] := by decide

theorem torusBracket_4 :
    torusBracket 4 = [(-10, -1), (-6, 1), (-2, -1), (6, -1)] := by decide

theorem torusBracket_5 :
    torusBracket 5 =
      [(-13, 1), (-9, -1), (-5, 1), (-1, -1), (7, -1)] := by decide

/-! ## Coefficient extraction -/

/-- `coefAt p e` returns the coefficient of `A^e` in the canonical
`LPoly p`; `0` if absent. -/
def coefAt : LPoly → Int → Int
  | [], _ => 0
  | (e', c') :: xs, e =>
      if e = e' then c'
      else if e < e' then 0
      else coefAt xs e

/-- Sanity: `coefAt` on `⟨T(2, 3)⟩ = A⁻⁷ - A⁻³ - A⁵`. -/
theorem coefAt_t23 :
    coefAt (torusBracket 3) (-7) = 1
    ∧ coefAt (torusBracket 3) (-3) = -1
    ∧ coefAt (torusBracket 3) 5 = -1
    ∧ coefAt (torusBracket 3) 0 = 0
    ∧ coefAt (torusBracket 3) 42 = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · decide
  · decide
  · decide
  · decide
  · decide

/-! ## Mod-`p` reduction of coefficients

We fold coefficients through `Int.emod` to `Nat` in `[0, p)`, drop
zero residues, and return `(exponent, residue)` pairs preserving
the ascending exponent order of the input. -/

/-- Reduce an `Int` coefficient to its representative in `[0, p)`
as a `Nat`.  Uses `Int.emod` so negative coefficients map to the
non-negative representative. -/
def intModNat (c : Int) (p : Nat) : Nat :=
  (c.emod (p : Int)).toNat

/-- `bracketModP p pl`: reduce each coefficient of `pl` mod `p`,
drop zero residues, keep ascending exponent order. -/
def bracketModP (p : Nat) : LPoly → List (Int × Nat)
  | [] => []
  | (e, c) :: xs =>
      let r := intModNat c p
      if r = 0 then bracketModP p xs
      else (e, r) :: bracketModP p xs

/-! ## Item 4: explicit `bracketModP` tables

`⟨T(2, 2)⟩ = -A⁻⁴ - A⁴`: every coefficient is `-1`, so every
residue is `p - 1`.

`⟨T(2, 3)⟩ = A⁻⁷ - A⁻³ - A⁵`; mixed `+1`/`-1` coefficients.

`⟨T(2, 4)⟩ = -A⁻¹⁰ + A⁻⁶ - A⁻² - A⁶`.

`⟨T(2, 5)⟩ = A⁻¹³ - A⁻⁹ + A⁻⁵ - A⁻¹ - A⁷`.

None of these has a coefficient divisible by `3`, `5`, or `7`;
every residue stays nonzero, so the length of the table equals
the length of the original bracket. -/

theorem bracketModP_t22_p3 :
    bracketModP 3 (torusBracket 2) = [(-4, 2), (4, 2)] := by decide

theorem bracketModP_t22_p5 :
    bracketModP 5 (torusBracket 2) = [(-4, 4), (4, 4)] := by decide

theorem bracketModP_t22_p7 :
    bracketModP 7 (torusBracket 2) = [(-4, 6), (4, 6)] := by decide

theorem bracketModP_t23_p3 :
    bracketModP 3 (torusBracket 3) = [(-7, 1), (-3, 2), (5, 2)] := by decide

theorem bracketModP_t23_p5 :
    bracketModP 5 (torusBracket 3) = [(-7, 1), (-3, 4), (5, 4)] := by decide

theorem bracketModP_t23_p7 :
    bracketModP 7 (torusBracket 3) = [(-7, 1), (-3, 6), (5, 6)] := by decide

theorem bracketModP_t24_p3 :
    bracketModP 3 (torusBracket 4)
      = [(-10, 2), (-6, 1), (-2, 2), (6, 2)] := by decide

theorem bracketModP_t24_p5 :
    bracketModP 5 (torusBracket 4)
      = [(-10, 4), (-6, 1), (-2, 4), (6, 4)] := by decide

theorem bracketModP_t24_p7 :
    bracketModP 7 (torusBracket 4)
      = [(-10, 6), (-6, 1), (-2, 6), (6, 6)] := by decide

theorem bracketModP_t25_p3 :
    bracketModP 3 (torusBracket 5)
      = [(-13, 1), (-9, 2), (-5, 1), (-1, 2), (7, 2)] := by decide

theorem bracketModP_t25_p5 :
    bracketModP 5 (torusBracket 5)
      = [(-13, 1), (-9, 4), (-5, 1), (-1, 4), (7, 4)] := by decide

theorem bracketModP_t25_p7 :
    bracketModP 7 (torusBracket 5)
      = [(-13, 1), (-9, 6), (-5, 1), (-1, 6), (7, 6)] := by decide

/-! ## Item 5: Fermat-flavored exponent-period probe (expected-negative)

For a prime `p`, if `A` were a unit of `(ℤ/p)^×` Fermat would force
`A^{p-1} ≡ 1 mod p`, and the mod-`p` coefficient at exponent `e`
would equal the mod-`p` coefficient at exponent `e mod (p - 1)`.
`A` is a formal Laurent variable, not a unit of `(ℤ/p)^×`, so we
expect this to fail.  We check concretely.

`exponentPeriodHolds p pl`: for every pair of exponents `e₁, e₂`
appearing in `bracketModP p pl` with `e₁ ≡ e₂ (mod p-1)`, the
residues at `e₁` and `e₂` must agree.  If the bracket contains
even one violation, the predicate is `false`.

For `p = 5, p - 1 = 4`: the exponents of `⟨T(2, 3)⟩` are
`{-7, -3, 5}` and `(-7) mod 4 = 1, (-3) mod 4 = 1, 5 mod 4 = 1`.
All three lie in the same residue class mod `4`, but their mod-5
residues are `1, 4, 4` — they do *not* all agree, so the probe
fails.  We report this negative fact. -/

/-- Are two integers congruent mod `m` (for `m > 0`)? -/
def intCongMod (e₁ e₂ : Int) (m : Nat) : Bool :=
  (e₁.emod (m : Int)).toNat = (e₂.emod (m : Int)).toNat

/-- Look up the mod-`p` residue of the `A^e`-coefficient. -/
def residueAt (pl : List (Int × Nat)) (e : Int) : Nat :=
  match pl with
  | [] => 0
  | (e', r) :: xs =>
      if e = e' then r else residueAt xs e

/-- For every pair of support exponents `e₁ ≡ e₂ (mod p - 1)`,
check whether their mod-`p` residues agree. -/
def exponentPeriodHolds (p : Nat) (pl : List (Int × Nat)) : Bool :=
  pl.all fun er₁ =>
    pl.all fun er₂ =>
      !(intCongMod er₁.1 er₂.1 (p - 1)) || (er₁.2 = er₂.2)

/-- Empirical status: for `T(2, 3)` at `p = 5`, the probe returns
`false`.  The three exponents `-7, -3, 5` all lie in the class
`1 mod 4`, yet their mod-5 residues `1, 4, 4` do not all agree.
Honest negative. -/
theorem exponent_period_t23_p5_fails :
    exponentPeriodHolds 5 (bracketModP 5 (torusBracket 3)) = false := by
  decide

/-- Same probe on `T(2, 4)` at `p = 5`: fails. -/
theorem exponent_period_t24_p5_fails :
    exponentPeriodHolds 5 (bracketModP 5 (torusBracket 4)) = false := by
  decide

/-- Same probe on `T(2, 5)` at `p = 3`: fails.  All five exponents
`-13, -9, -5, -1, 7` are odd, so they all lie in the single
class `1 mod 2`, while their mod-3 residues mix `1` and `2`. -/
theorem exponent_period_t25_p3_fails :
    exponentPeriodHolds 3 (bracketModP 3 (torusBracket 5)) = false := by
  decide

/-- By contrast, `T(2, 2)` at `p = 3` happens to pass: its two
exponents `-4, 4` share the class `0 mod 2` and their mod-3
residues agree (both `2`).  A coincidence forced by the symmetric
`[-1, -1]` coefficient pattern. -/
theorem exponent_period_t22_p3_passes :
    exponentPeriodHolds 3 (bracketModP 3 (torusBracket 2)) = true := by
  decide

/-! ## Item 6: writhe mod `p - 1` on the normalized bracket

Recall `X(L) = (-A)^(-3 w(L)) · ⟨L⟩` from
`JonesPolynomialNormalization`.  Positive Hopf has `w = 2`,
normalized bracket `X(Hopf+) = -A⁻¹⁰ - A⁻²`.  Negative Hopf has
`w = -2`, normalized bracket `X(Hopf-) = -A² - A¹⁰`.  Writhes
differ by `4`, and `(-A)^(-3 · 4) = A⁻¹²`, so the two normalized
brackets are related by `X(Hopf+) = A⁻¹² · X(Hopf-)` — which, under
the formal substitution `A^4 = 1`, becomes
`X(Hopf+) = A⁰ · X(Hopf-) = X(Hopf-)`.

We witness this by folding both normalized brackets through
`foldA 4` (collapse every exponent to `[0, 4)`) and reducing
coefficients mod `5`.  The two tables coincide. -/

/-- `(-1)^n` for `n : Int`. -/
def negOnePow (n : Int) : Int :=
  if n % 2 = 0 then 1 else -1

/-- `(-A)^n` as an `LPoly`. -/
def negAPow (n : Int) : LPoly :=
  [(n, negOnePow n)]

/-- `X(L) = (-A)^(-3 w) · ⟨L⟩`. -/
def normalizedBracket (w : Int) (bracket : LPoly) : LPoly :=
  mulP (negAPow (-3 * w)) bracket

/-- Positive Hopf bracket, matching
`JonesPolynomialNormalization.hopfBracket` and the `n = 2` case
of `torusBracket` above. -/
def hopfBracketLit : LPoly := [(-4, -1), (4, -1)]

theorem hopfBracketLit_agrees :
    hopfBracketLit = torusBracket 2 := by decide

/-- Normalized bracket for Hopf+ (writhe `+2`): `-A⁻¹⁰ - A⁻²`. -/
def hopfPosNormBracket : LPoly :=
  normalizedBracket 2 hopfBracketLit

/-- Normalized bracket for Hopf- (writhe `-2`): `-A² - A¹⁰`. -/
def hopfNegNormBracket : LPoly :=
  normalizedBracket (-2) hopfBracketLit

theorem hopfPosNormBracket_value :
    hopfPosNormBracket = [(-10, -1), (-2, -1)] := by decide

theorem hopfNegNormBracket_value :
    hopfNegNormBracket = [(2, -1), (10, -1)] := by decide

/-- Collapse an exponent onto its representative in `[0, m)`. -/
def foldExp (e : Int) (m : Nat) : Int :=
  e.emod (m : Int)

/-- Fold an `LPoly` under `A^m = 1` by mapping each exponent to
its representative in `[0, m)` and re-aggregating via
`insertMono`. -/
def foldA (m : Nat) : LPoly → LPoly
  | [] => []
  | (e, c) :: xs => insertMono (foldExp e m) c (foldA m xs)

/-- Combine `foldA (p - 1)` (fold under `A^{p-1} = 1`) with
`bracketModP p` (reduce coefs mod `p`).  The result is a
normalized "residue vector" living in the finite set of maps
`[0, p - 1) → [0, p)`. -/
def foldAndReduce (p : Nat) (pl : LPoly) : List (Int × Nat) :=
  bracketModP p (foldA (p - 1) pl)

/-- Sanity: the bare `⟨T(2, 2)⟩ = -A⁻⁴ - A⁴` collapses under
`A^4 = 1` onto two monomials at `A^0`, giving `-2 · A^0`, reduced
mod `5` to residue `3`. -/
theorem foldAndReduce_t22_p5 :
    foldAndReduce 5 (torusBracket 2) = [(0, 3)] := by decide

/-- **Writhe mod `(p - 1)` witness.**  At `p = 5`, folding the two
normalized Hopf brackets under `A^4 = 1` and reducing coefficients
mod `5` yields the *same* residue table for Hopf+ and Hopf-.  The
writhe-shift `(-A)^(-3 · 4) = A⁻¹²` that distinguishes them in
`ℤ[A, A⁻¹]` collapses to `A^0` under `A^4 = 1`. -/
theorem writhe_mod_pminus1_hopf_collapse_p5 :
    foldAndReduce 5 hopfPosNormBracket
      = foldAndReduce 5 hopfNegNormBracket := by decide

/-- The common collapsed residue table: `[(2, 3)]`, i.e. `-2 · A²`
reduced to residue `3 · A²` mod 5, on the folded `[0, 4)` strip. -/
theorem writhe_mod_pminus1_hopf_common_table_p5 :
    foldAndReduce 5 hopfPosNormBracket = [(2, 3)] := by decide

/-- Comparison: the *bare* (un-normalized) Hopf bracket folds to
`[(0, 3)]`, at exponent `0` rather than at exponent `2`.  The
writhe normalization shifts the support exponent by `2` on the
folded strip — a difference visible to `foldAndReduce`, but one
that cancels exactly when comparing Hopf+ to Hopf- (both land at
exponent `2`). -/
theorem writhe_mod_pminus1_bare_vs_normalized_p5 :
    foldAndReduce 5 (torusBracket 2) = [(0, 3)]
    ∧ foldAndReduce 5 hopfPosNormBracket = [(2, 3)]
    ∧ foldAndReduce 5 hopfNegNormBracket = [(2, 3)] := by
  refine ⟨?_, ?_, ?_⟩
  · decide
  · decide
  · decide

/-! ## Item 7: Torus-link Chebyshev period mod `p`

The `(2, n)` bracket satisfies the Chebyshev-like recurrence
`b_{n+1} = (A - A⁻³) · b_n + A⁻² · b_{n-1}` from
`TorusKnotChebyshevBracket.cheb_recurrence_at_{2,3,4}`.

We reduce the recurrence modulo `p` and fold exponents under
`A^{p-1} = 1`: every step computes
`foldAndReduce p (addP (mulP chebAlpha b_n) (mulP chebBeta b_{n-1}))`.
The sequence `(b̄_n)` lives in the finite set of maps
`[0, p - 1) → [0, p)`, so it is eventually periodic.

### Empirical periods

Seed `b̄₁ = foldAndReduce p ⟨T(2, 1)⟩`,
`b̄₂ = foldAndReduce p ⟨T(2, 2)⟩`.  The sequence iterates as:

* `p = 3`: `b̄₁ = [(1, 2)]`, `b̄₂ = [(0, 1)]`, and the sequence
  alternates these two — period `2`.
* `p = 5`: `b̄₁ = [(3, 4)]`, `b̄₂ = [(0, 3)]`, then `[(1, 4)]`,
  `[(2, 3)]`, back to `[(3, 4)]` — period `4`.
* `p = 7`: `b̄₁ = [(3, 6)]`, `b̄₂ = [(2, 6), (4, 6)]`, and the
  sequence alternates — period `2`.

### Empirical surprise

At `p = 3` and `p = 5` the period equals `p - 1`.  At `p = 7` it
does *not* — the period is `2`, much shorter than `p - 1 = 6`.
The Chebyshev-like recurrence `(A - A⁻³, A⁻²)` reduced mod 7 and
folded at `A^6 = 1` admits a size-`2` orbit from the torus seed.
We report this collapse, not a general law. -/

/-- Chebyshev-like linear coefficient `α = A - A⁻³`. -/
def chebAlpha : LPoly := [(-3, -1), (1, 1)]

/-- Chebyshev-like constant coefficient `β = A⁻²`. -/
def chebBeta : LPoly := [(-2, 1)]

/-- Convert a reduced list `List (Int × Nat)` back to an `LPoly` by
lifting residues to signed `Int` coefficients, preserving
canonical ordering. -/
def liftRes (rs : List (Int × Nat)) : LPoly :=
  rs.foldr (fun (er : Int × Nat) acc =>
    insertMono er.1 (Int.ofNat er.2) acc) []

/-- One step of the recurrence, folded and reduced: given the
previous two terms in `LPoly` form, produce the next term already
folded and reduced and lifted back to an `LPoly`. -/
def chebStep (p : Nat) (bnm1 bn : LPoly) : LPoly :=
  let next := addP (mulP chebAlpha bn) (mulP chebBeta bnm1)
  liftRes (foldAndReduce p next)

/-- Iterate `chebStep` `k` times, producing a list of length
`k + 2` starting from `b₁, b₂` (all folded-and-reduced). -/
def chebSeq (p : Nat) : Nat → LPoly → LPoly → List LPoly
  | 0,           b1, b2 => [b1, b2]
  | Nat.succ k,  b1, b2 =>
      let b3 := chebStep p b1 b2
      b1 :: chebSeq p k b2 b3

/-- Seed `b̄₁`. -/
def chebSeed1 (p : Nat) : LPoly :=
  liftRes (foldAndReduce p (torusBracket 1))

/-- Seed `b̄₂`. -/
def chebSeed2 (p : Nat) : LPoly :=
  liftRes (foldAndReduce p (torusBracket 2))

/-- Index-safe access on a `List LPoly`; default `[]`. -/
def nthPoly : List LPoly → Nat → LPoly
  | [],       _ => []
  | p :: _,   0 => p
  | _ :: xs,  Nat.succ k => nthPoly xs k

/-! ### Seed sanity -/

theorem chebSeed1_p3 : chebSeed1 3 = [(1, 2)] := by decide

theorem chebSeed2_p3 : chebSeed2 3 = [(0, 1)] := by decide

theorem chebSeed1_p5 : chebSeed1 5 = [(3, 4)] := by decide

theorem chebSeed2_p5 : chebSeed2 5 = [(0, 3)] := by decide

theorem chebSeed1_p7 : chebSeed1 7 = [(3, 6)] := by decide

theorem chebSeed2_p7 : chebSeed2 7 = [(2, 6), (4, 6)] := by decide

/-! ### Period `2` at `p = 3` -/

def chebWindow3 : List LPoly :=
  chebSeq 3 10 (chebSeed1 3) (chebSeed2 3)

/-- `b̄₁ = b̄₃` at `p = 3` (period `2` hit). -/
theorem cheb_period_p3_at_1 :
    nthPoly chebWindow3 0 = nthPoly chebWindow3 2 := by decide

/-- `b̄₂ = b̄₄` at `p = 3`. -/
theorem cheb_period_p3_at_2 :
    nthPoly chebWindow3 1 = nthPoly chebWindow3 3 := by decide

/-- Period is minimal: `b̄₁ ≠ b̄₂` at `p = 3`. -/
theorem cheb_period_p3_minimal :
    nthPoly chebWindow3 0 ≠ nthPoly chebWindow3 1 := by decide

/-! ### Period `4` at `p = 5` -/

def chebWindow5 : List LPoly :=
  chebSeq 5 12 (chebSeed1 5) (chebSeed2 5)

/-- `b̄₁ = b̄₅` at `p = 5` (period `4` hit). -/
theorem cheb_period_p5_at_1 :
    nthPoly chebWindow5 0 = nthPoly chebWindow5 4 := by decide

/-- `b̄₂ = b̄₆` at `p = 5`. -/
theorem cheb_period_p5_at_2 :
    nthPoly chebWindow5 1 = nthPoly chebWindow5 5 := by decide

/-- Period is minimal: none of the shifts `1, 2, 3` match. -/
theorem cheb_period_p5_minimal :
    nthPoly chebWindow5 0 ≠ nthPoly chebWindow5 1
    ∧ nthPoly chebWindow5 0 ≠ nthPoly chebWindow5 2
    ∧ nthPoly chebWindow5 0 ≠ nthPoly chebWindow5 3 := by
  refine ⟨?_, ?_, ?_⟩
  · decide
  · decide
  · decide

/-! ### Period `2` at `p = 7` (empirical collapse from `p - 1 = 6`) -/

def chebWindow7 : List LPoly :=
  chebSeq 7 12 (chebSeed1 7) (chebSeed2 7)

/-- `b̄₁ = b̄₃` at `p = 7` — period `2`, not `p - 1 = 6`. -/
theorem cheb_period_p7_at_1 :
    nthPoly chebWindow7 0 = nthPoly chebWindow7 2 := by decide

/-- `b̄₂ = b̄₄` at `p = 7`. -/
theorem cheb_period_p7_at_2 :
    nthPoly chebWindow7 1 = nthPoly chebWindow7 3 := by decide

/-- Period is minimal: `b̄₁ ≠ b̄₂` at `p = 7`. -/
theorem cheb_period_p7_minimal :
    nthPoly chebWindow7 0 ≠ nthPoly chebWindow7 1 := by decide

/-- The `p = 7` period does *not* equal `p - 1`: we witness an
offset-4 disagreement (if period were `6`, `b̄₁` would equal
`b̄₇` first, and `b̄₁ ≠ b̄₅` is a free corollary of period `2`
with `b̄₅ = b̄₁ · (period-shift-4 via period-2)` — encoded here
as an explicit index-4 comparison that collapses to period 2
identity, i.e. `b̄₁ = b̄₅`). -/
theorem cheb_period_p7_collapses_below_pminus1 :
    nthPoly chebWindow7 0 = nthPoly chebWindow7 4 := by decide

/-! ## Combined witness -/

/-- Aggregated witness: bracket values for `n = 1..5`, mod-`p`
reduction tables at `p = 3, 5, 7`, the Fermat-flavored
exponent-period probe (honest negative on generic brackets), the
writhe mod `(p - 1)` collapse on the Hopf normalized brackets at
`p = 5`, and the Chebyshev-like periods `2, 4, 2` at
`p = 3, 5, 7`. -/
theorem jones_mod_p_fermat_witness :
    torusBracket 2 = [(-4, -1), (4, -1)]
    ∧ bracketModP 5 (torusBracket 2) = [(-4, 4), (4, 4)]
    ∧ exponentPeriodHolds 3 (bracketModP 3 (torusBracket 2)) = true
    ∧ exponentPeriodHolds 5 (bracketModP 5 (torusBracket 3)) = false
    ∧ foldAndReduce 5 hopfPosNormBracket
        = foldAndReduce 5 hopfNegNormBracket
    ∧ foldAndReduce 5 hopfPosNormBracket = [(2, 3)]
    ∧ nthPoly chebWindow3 0 = nthPoly chebWindow3 2
    ∧ nthPoly chebWindow5 0 = nthPoly chebWindow5 4
    ∧ nthPoly chebWindow7 0 = nthPoly chebWindow7 2 := by
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

end JonesModPFermat
end BuleyeanMath
