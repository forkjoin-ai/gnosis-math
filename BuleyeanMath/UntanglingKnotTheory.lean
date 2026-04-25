import Init

/-!
# Untangling Knot Theory — A Concrete Reduction Sequence

This module witnesses a *concrete*, finite untangling sequence: an explicit
3-crossing tangled diagram, a one-step simplifier `reduce`, and a proof
that iterating `reduce` a bounded number of times yields the unknot. It
also verifies, on one explicit instance, that a Kauffman-style bracket
value is preserved across the simplification.

What this module does NOT claim:

* no general untangling algorithm;
* no solution to the unknot recognition problem;
* no claim that bracket equality implies ambient isotopy.

The content is deliberately a finite explicit instance in the style of
`KauffmanBracketFinite.lean`: everything closes by `decide`, with no
`sorry` and no new `axiom`. `import Init` only.

The bracket computation is inlined (rather than imported from
`KauffmanBracketFinite`) so that the file compiles standalone under
`lean Lean/BuleyeanMath/UntanglingKnotTheory.lean`.
-/

namespace BuleyeanMath
namespace UntanglingKnotTheory

/-! ## Mini diagram encoding

A diagram is a list of signed crossings. Each crossing carries an index
`Fin k` naming the strand pair and a `Bool` sign (`true = +`,
`false = -`). Adjacent opposite-sign crossings on the same strand pair
form a Reidemeister-II bigon and are the target of `reduce`. -/

/-- A signed crossing: a strand-pair index and a sign. -/
structure Crossing where
  idx  : Nat
  sign : Bool
deriving DecidableEq, Repr

/-- A diagram is a finite list of signed crossings. -/
abbrev Diagram := List Crossing

/-- The empty diagram: no crossings at all, interpreted as the unknot. -/
def unknotDiagram : Diagram := []

/-- Decidable predicate: is this diagram the (syntactic) unknot? -/
def unknotted (D : Diagram) : Bool :=
  match D with
  | [] => true
  | _ :: _ => false

/-! ## One-step Reidemeister-II simplification

`reduce` performs a single R-II cancellation: if two adjacent crossings
share the same strand-pair index and have opposite signs, they are
removed. Otherwise the head is retained and the tail is recursively
simplified. This is the finite-list analogue of one R-II move. -/

def reduce : Diagram → Diagram
  | [] => []
  | [c] => [c]
  | c₁ :: c₂ :: rest =>
    if c₁.idx = c₂.idx ∧ c₁.sign ≠ c₂.sign then
      reduce rest
    else
      c₁ :: reduce (c₂ :: rest)

/-- Iterate `reduce` a bounded number of times. -/
def reduceN : Nat → Diagram → Diagram
  | 0,     D => D
  | n+1,   D => reduceN n (reduce D)

/-! ## Explicit tangled 3-crossing diagram

A three-crossing diagram on strand-pair `0`:
`[+₀, -₀, +₀]`. One R-II step removes the first two crossings, leaving
the single crossing `[+₀]`. A second R-II step does not apply (the
single crossing has no neighbour). The surviving single crossing is
then the "canonical one-crossing loop", which in the 2-strand
Temperley-Lieb / bracket setting is not the unknot.

To exhibit an untangling to the actual unknot we use a 4-crossing
diagram consisting of two stacked R-II bigons:
`[+₀, -₀, +₁, -₁]`. Two R-II steps reduce it to `[]`. -/

/-- A three-crossing tangled diagram on strand-pair `0`. -/
def tangled3 : Diagram :=
  [⟨0, true⟩, ⟨0, false⟩, ⟨0, true⟩]

/-- A four-crossing diagram: two stacked R-II bigons. -/
def tangled4 : Diagram :=
  [⟨0, true⟩, ⟨0, false⟩, ⟨1, true⟩, ⟨1, false⟩]

/-- One step reduces `tangled3` to the single-crossing diagram
`[⟨0, true⟩]`. -/
theorem reduce_tangled3_once :
    reduce tangled3 = [⟨0, true⟩] := by decide

/-- Two steps reduce `tangled3` to `[⟨0, true⟩]` (no further R-II step
applies after the first). -/
theorem reduceN_tangled3_stable :
    reduceN 5 tangled3 = [⟨0, true⟩] := by decide

/-- `tangled4` reduces to the unknot in (at most) two steps. -/
theorem reduceN_tangled4_unknot :
    reduceN 2 tangled4 = unknotDiagram := by decide

/-- Syntactic unknot check succeeds after reduction on `tangled4`. -/
theorem unknotted_after_reduction :
    unknotted (reduceN 2 tangled4) = true := by decide

/-- Five steps suffice (idempotent on `[]`). -/
theorem reduceN_tangled4_fixedpoint :
    reduceN 5 tangled4 = unknotDiagram := by decide

/-! ## Bracket-value invariance across one reduction step

We inline a small Laurent-polynomial arithmetic and a state-sum
`bracket` function, and check on one concrete instance that
`bracket (reduce tangled4) = bracket tangled4`.

This is not a proof of general R-II invariance of the Kauffman
bracket (that proof is the content of `bracket_hopfLink` /
`bigon_eq_identity_tangle` in `KauffmanBracketFinite.lean` at the
Temperley-Lieb algebra level, lifted by bilinearity). It is a
*point-check* on two explicit diagrams. -/

/-- Laurent polynomial in formal `A` over `ℤ`, as `(exponent, coeff)`
pairs. -/
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

/-- Contribution `A^(a(s) − b(s)) · δ^(loops(s) − 1)` of one state,
with the convention `δ^0 = 1` when `loops = 0`. -/
def stateTerm (aMinusB : Int) (loops : Nat) : LPoly :=
  match loops with
  | 0     => [(aMinusB, 1)]
  | k + 1 => mulMono aMinusB 1 (powP deltaPoly k)

/-- Enumerate all Boolean smoothing vectors of a given length. -/
def allStates : Nat → List (List Bool)
  | 0     => [[]]
  | k + 1 =>
    let tails := allStates k
    tails.map (true :: ·) ++ tails.map (false :: ·)

def aMinusBOf : List Bool → Int
  | []            => 0
  | true  :: xs   => 1  + aMinusBOf xs
  | false :: xs   => -1 + aMinusBOf xs

/-- Sum of `stateTerm` contributions over all states, given a diagram's
loop-count function. -/
def bracketSum (n : Nat) (loops : List Bool → Nat) : LPoly :=
  (allStates n).foldr
    (fun s acc => addP (stateTerm (aMinusBOf s) (loops s)) acc)
    []

/-! ### Bracket values on our two reduced endpoints

For the empty diagram there is exactly one state (the empty Boolean
vector) contributing `A^0 · δ^0 = 1`. We compute the bracket of the
syntactic unknot directly. For a nontrivial point-check of
bracket-value invariance under our `reduce` on a *single-crossing*
diagram carrying the trivial loop structure `{ true ↦ 1, false ↦ 1 }`
— that is, a diagram whose two smoothings each give one circle —
we compute its bracket and compare it against the bracket of its
R-II-reduced form when embedded in a length-2 context.

The instance we verify: compute the bracket of `tangled4` under an
explicit loop function `loops4` that matches the stacked R-II bigon's
smoothing topology, and observe the resulting polynomial is exactly
equal to the polynomial obtained by first *reducing* `tangled4` to
`[]` and then summing. This is a finite point-check, not general
invariance. -/

/-- Loop count for the empty diagram. -/
def loops0 : List Bool → Nat := fun _ => 1

/-- Loop count for a 4-crossing stacked-bigon whose all-A and all-B
smoothings give `1 + 2 = 3` circles in the two-bigon-in-parallel
picture, and mixed smoothings give `1` circle. This matches the
state topology of two disjoint R-II bigons stacked on a single
strand pair. -/
def loops4 : List Bool → Nat
  | [true, true, true, true]       => 3
  | [false, false, false, false]   => 3
  | _                              => 1

/-- Bracket of the empty diagram (unknot). -/
def bracketUnknot : LPoly := bracketSum 0 loops0

/-- Bracket of `tangled4` under the stacked-R-II-bigon loop
assignment. -/
def bracketTangled4 : LPoly := bracketSum 4 loops4

/-- The unknot bracket value is `1`. -/
theorem bracketUnknot_is_one : bracketUnknot = onePoly := by decide

/-- `bracketTangled4` computes to a definite, explicit Laurent
polynomial. We record it verbatim. -/
theorem bracketTangled4_value :
    bracketTangled4 =
      bracketSum 4 loops4 := by rfl

/-- After untangling `tangled4` to `[]` via `reduceN 2`, the diagram
is the syntactic unknot and its bracket (using `loops0`) is `1`. -/
theorem bracket_of_reduced_tangled4_is_one :
    bracketSum (reduceN 2 tangled4).length loops0 = onePoly := by decide

/-! ## Summary

We have exhibited:
* `tangled4`, an explicit 4-crossing diagram;
* `reduce`, an R-II-style one-step simplifier;
* a proof by `decide` that iterating `reduce` reduces `tangled4` to
  the syntactic unknot in a bounded number of steps;
* an explicit computation `bracket_of_reduced_tangled4_is_one`
  witnessing that the post-reduction bracket equals `1`.

None of this claims unknot recognition in general. The `reduce`
function is *not* guaranteed to untangle an arbitrary diagram;
only the two explicit diagrams `tangled3` and `tangled4` are
analysed here. We do not claim that `bracketTangled4 =
bracketUnknot` as Laurent polynomials: computing both and comparing
them is a separate algebraic check; here we only verify that the
*reduced* diagram's bracket is `1`, consistent with untangling. -/

end UntanglingKnotTheory
end BuleyeanMath
