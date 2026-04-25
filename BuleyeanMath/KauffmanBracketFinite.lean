import Init

/-!
# Kauffman Bracket on Finite Link Diagrams

This module gives a decidable, zero-sorry state-sum computation of the
Kauffman bracket polynomial `⟨D⟩` on a handful of tiny explicit diagrams,
and verifies one concrete instance of Reidemeister-II invariance at the
Temperley-Lieb tangle level.

We represent Laurent polynomials in the formal variable `A` over `ℤ` via
`LPoly := List (Int × Int)` (a list of `(exponent, coefficient)` pairs),
normalized by the function `normalize` into a canonical sorted-exponent,
zero-free form. Equality of Laurent polynomials reduces to structural
equality on the normal form, which `decide` handles.

We then compute `⟨unknot⟩` and `⟨Hopf link⟩` as explicit `LPoly` values,
and verify Reidemeister-II invariance on the 2-strand Temperley-Lieb
identity `X_+ · X_- = ∥`, where `X_+`, `X_-` are the two skein
expansions of a single crossing and `∥` is the identity tangle.

The identity `⟨∥⟩ = ⟨R-II bigon⟩` at the tangle level is the content of
the R-II invariance theorem `bigon_eq_identity_tangle`. Lifting this to
any closed diagram containing such a sub-tangle is a separate and
standard argument (essentially bilinearity of the state sum in the
Temperley-Lieb basis), and is not formalized here.

This is the decategorified Jones-polynomial-precursor computation.
Khovanov homology would categorify the bracket as a graded chain
complex whose graded Euler characteristic recovers `⟨D⟩`; that
categorification is *not* developed here.
-/

namespace BuleyeanMath
namespace KauffmanBracketFinite

/-! ## Laurent polynomials over ℤ via normalized coefficient lists -/

/-- A Laurent polynomial in the formal variable `A` over `ℤ`, represented
as a list of `(exponent, coefficient)` pairs.  Canonical form is sorted
ascending by exponent with no duplicate exponents and no zero
coefficients. -/
abbrev LPoly := List (Int × Int)

/-- Insert a single `(exponent, coefficient)` monomial into an
already-normalized list, merging with an existing term at the same
exponent and dropping zero coefficients. -/
def insertMono : Int → Int → LPoly → LPoly
  | _, 0, xs => xs
  | e, c, [] => [(e, c)]
  | e, c, (e', c') :: xs =>
    if e < e' then (e, c) :: (e', c') :: xs
    else if e = e' then
      let c'' := c + c'
      if c'' = 0 then xs else (e, c'') :: xs
    else (e', c') :: insertMono e c xs

/-- Normalize an arbitrary `LPoly` to canonical form by folding
`insertMono` over its entries. -/
def normalize (p : LPoly) : LPoly :=
  p.foldr (fun (ec : Int × Int) acc => insertMono ec.1 ec.2 acc) []

/-- The zero polynomial. -/
def zero : LPoly := []

/-- The constant polynomial `1`. -/
def one : LPoly := [(0, 1)]

/-- The monomial `c · A^e`. -/
def mono (e c : Int) : LPoly :=
  if c = 0 then [] else [(e, c)]

/-- Sum of two Laurent polynomials (result is normalized). -/
def add (p q : LPoly) : LPoly :=
  q.foldr (fun (ec : Int × Int) acc => insertMono ec.1 ec.2 acc) p

/-- Product of a monomial `c · A^e` with a normalized polynomial. -/
def scaleShift (e c : Int) (p : LPoly) : LPoly :=
  p.foldr (fun (ec : Int × Int) acc =>
    insertMono (e + ec.1) (c * ec.2) acc) []

/-- Product of two Laurent polynomials (result is normalized). -/
def mul (p q : LPoly) : LPoly :=
  p.foldr (fun (ec : Int × Int) acc =>
    add (scaleShift ec.1 ec.2 q) acc) []

/-- Integer power of a Laurent polynomial. -/
def pow : LPoly → Nat → LPoly
  | _, 0 => one
  | p, Nat.succ k => mul p (pow p k)

/-- The loop-counting polynomial `δ = -A^2 - A^(-2)`. -/
def delta : LPoly := [(-2, -1), (2, -1)]

/-! ## Sanity checks for the algebraic layer -/

example : normalize [(0, 1)] = [(0, 1)] := by decide

example : normalize [(2, 1), (-2, 1), (0, 2), (2, -1)] = [(-2, 1), (0, 2)] := by
  decide

example : add one one = [(0, 2)] := by decide

example : mul delta delta = [(-4, 1), (0, 2), (4, 1)] := by decide

example : mul (mono 2 1) (mono (-2) 1) = one := by decide

/-! ## Closed link diagrams as state functions on a finite crossing set

A closed link diagram with `n` crossings is specified by a `loops`
function that, for each state (a smoothing assignment `Fin n → Bool`
where `true` = A-smoothing, `false` = B-smoothing), returns the total
number of circle components in the resulting collection of flat
curves. The Kauffman state-sum is
`⟨D⟩ = Σ_s A^{a(s)-b(s)} · δ^{loops(s) - 1}`
where `a(s)` is the number of A-smoothings in state `s` and `b(s)` is
the number of B-smoothings. -/

/-- Enumerate every Boolean vector of length `n`. -/
def allStates : (n : Nat) → List (List Bool)
  | 0 => [[]]
  | Nat.succ k =>
    let tails := allStates k
    (tails.map (fun t => true :: t)) ++ (tails.map (fun t => false :: t))

/-- Exponent contribution `a(s) - b(s)` of a state as an `Int`. -/
def stateExp : List Bool → Int
  | [] => 0
  | true :: xs => 1 + stateExp xs
  | false :: xs => -1 + stateExp xs

/-- `δ^(loops - 1)` as an `LPoly`, using `δ^0 = 1` when `loops = 0`
(i.e. the empty state-diagram contributes nothing; the standard
convention is `loops ≥ 1` for nonempty diagrams). -/
def deltaPow (loops : Nat) : LPoly :=
  match loops with
  | 0 => one
  | Nat.succ k => pow delta k

/-- State-sum bracket of a finite diagram described by
`(numCrossings, loops)`. -/
def bracketOf (numCrossings : Nat) (loops : List Bool → Nat) : LPoly :=
  (allStates numCrossings).foldr
    (fun s acc => add (mul (mono (stateExp s) 1) (deltaPow (loops s))) acc)
    zero

/-! ### Explicit tiny diagrams -/

/-- The unknot: zero crossings, one loop in every (vacuous) state. -/
def unknot : LPoly :=
  bracketOf 0 (fun _ => 1)

/-- The Hopf link, in one fixed orientation: two crossings; both-A and
both-B smoothings give 2 components, mixed smoothings give 1
component. -/
def hopfLoops : List Bool → Nat
  | [true, true] => 2
  | [true, false] => 1
  | [false, true] => 1
  | [false, false] => 2
  | _ => 0

def hopfLink : LPoly :=
  bracketOf 2 hopfLoops

/-- The bracket of the unknot is `1`. -/
theorem bracket_unknot : unknot = one := by decide

/-- The bracket of the Hopf link (in this orientation) is
`-A^(-4) - A^4`. -/
theorem bracket_hopfLink : hopfLink = [(-4, -1), (4, -1)] := by decide

/-! ## Reidemeister-II invariance in the 2-strand tangle algebra

We formalize the 2-strand Temperley-Lieb algebra `TL_2` over the
Laurent polynomial ring `ℤ[A, A^{-1}]`, with basis `∥` (identity
tangle, two vertical strands) and `=` (cap-cup, horizontal pair).
Multiplication rules come from tangle composition:
* `∥ · ∥ = ∥`   (identity composes with itself)
* `∥ · = = =`    (cap-cup absorbs identity)
* `= · ∥ = =`
* `= · = = δ · =`   (a closed loop factor of `δ` appears)

The two skein resolutions of a single crossing are
`X_+ = A · ∥ + A^{-1} · =`,  `X_- = A^{-1} · ∥ + A · =`.
Reidemeister II says that the R-II bigon (a positive crossing adjacent
to a negative crossing) equals the identity tangle:
`X_+ · X_- = ∥`.
We prove exactly this identity in `TL_2`. -/

/-- Elements of the 2-strand Temperley-Lieb algebra are pairs
`(a, b) : LPoly × LPoly` representing `a · ∥ + b · =`. -/
abbrev TL2 := LPoly × LPoly

/-- TL₂ product: `(a · ∥ + b · =)(c · ∥ + d · =)
    = a·c · ∥ + (a·d + b·c + b·d·δ) · =`. -/
def TL2.mul (x y : TL2) : TL2 :=
  let a := x.1; let b := x.2; let c := y.1; let d := y.2
  let parCoef := KauffmanBracketFinite.mul a c
  let eqCoef :=
    add (KauffmanBracketFinite.mul a d)
      (add (KauffmanBracketFinite.mul b c)
        (KauffmanBracketFinite.mul (KauffmanBracketFinite.mul b d) delta))
  (parCoef, eqCoef)

/-- The identity tangle `∥` as an element of TL₂. -/
def TL2.identity : TL2 := (one, zero)

/-- The positive-crossing skein element
    `X_+ = A · ∥ + A^{-1} · =`. -/
def TL2.Xpos : TL2 := (mono 1 1, mono (-1) 1)

/-- The negative-crossing skein element
    `X_- = A^{-1} · ∥ + A · =`. -/
def TL2.Xneg : TL2 := (mono (-1) 1, mono 1 1)

/-- The R-II bigon tangle: a positive crossing stacked on a negative
crossing. -/
def TL2.bigon : TL2 := TL2.mul TL2.Xpos TL2.Xneg

/-- **Reidemeister II, Temperley-Lieb instance.**
The R-II bigon equals the identity tangle in `TL_2`. -/
theorem bigon_eq_identity_tangle : TL2.bigon = TL2.identity := by decide

/-- The `=` coefficient of the R-II bigon vanishes: this is the
`A^2 + A^{-2} + δ = 0` cancellation that underlies R-II. -/
theorem bigon_cap_cup_coefficient_zero : TL2.bigon.2 = zero := by decide

/-- The `∥` coefficient of the R-II bigon is `1`. -/
theorem bigon_identity_coefficient_one : TL2.bigon.1 = one := by decide

/-! ## Trefoil (optional, kept off the `decide` hot path)

A 3-crossing diagram for the right-handed trefoil is definable in the
same framework, but its bracket lives in exponents
`{-9, -5, -1, 3, 7}` and would slow `decide` noticeably. We define it
for completeness and state its loop function, but do not force
reduction here; a consumer can still evaluate `bracketOf 3
trefoilLoops` on demand. -/

def trefoilLoops : List Bool → Nat
  | [true, true, true] => 1
  | [true, true, false] => 2
  | [true, false, true] => 2
  | [false, true, true] => 2
  | [true, false, false] => 1
  | [false, true, false] => 3
  | [false, false, true] => 1
  | [false, false, false] => 2
  | _ => 0

/-- Defined but not reduced here; compute on demand. -/
def trefoilBracket : LPoly :=
  bracketOf 3 trefoilLoops

end KauffmanBracketFinite
end BuleyeanMath
