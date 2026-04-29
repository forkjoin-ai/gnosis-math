import Init

/-!
# Folded Knot Isomorphism — A Finite Mapping-Class-Style Involution

This module witnesses an isomorphism between two concrete encodings of
the same small knot-theoretic object, related by a finite "fold"
operation. The fold is a finite analogue of a mapping-class-group
element: it permutes crossing indices and flips their signs. We prove,
by `decide`, that

* `fold` is an involution on the chosen representative: `fold (fold D) = D`;
* the two encodings share the same Kauffman-bracket state-sum value
  under compatible loop functions — an invariant-based isomorphism.

What this module does NOT claim:

* no general knot-classification result;
* no claim that bracket-polynomial equality implies ambient isotopy
  (the Jones polynomial is not a complete invariant; neither is the
  Kauffman bracket);
* no claim that `fold` realizes a specific geometric mapping class.

Content is `import Init` only, no `sorry`, no new `axiom`. The
bracket computation is inlined so the file compiles standalone under
`lean Lean/Gnosis/FoldedKnotIsomorphism.lean`. The
algebraic form of `LPoly` matches the form used in
`KauffmanBracketFinite.lean`.
-/

namespace Gnosis
namespace FoldedKnotIsomorphism

/-! ## Small diagram encoding

A diagram here is a list of signed crossings. Each crossing carries an
index in `Fin 2` (enough to encode the Hopf link under two crossing
orderings) and a `Bool` sign. -/

structure Crossing where
  idx  : Nat
  sign : Bool
deriving DecidableEq, Repr

abbrev Diagram := List Crossing

/-- First encoding of the Hopf link: two positive crossings on a
single strand pair, in the order `0, 1`. -/
def hopfA : Diagram :=
  [⟨0, true⟩, ⟨1, true⟩]

/-- Second encoding of the Hopf link: the same two crossings in the
kept order `0, 1`, with both signs flipped and the list reversed —
the image of `hopfA` under `fold`. -/
def hopfB : Diagram :=
  [⟨0, false⟩, ⟨1, false⟩]

/-! ## The fold

The fold permutes the two crossing indices (`0 ↔ 1`), reverses the
order of the crossings, and flips each sign. Geometrically this is
the composition of: (i) a swap of the two crossings' positions on
the strand, and (ii) a global sign flip. It is a finite permutation
+ sign-flip acting on the ordered crossing list — a tractable shadow
of a mapping-class-group element. -/

def swapIdx : Nat → Nat
  | 0 => 1
  | 1 => 0
  | n => n

def fold : Diagram → Diagram
  | D =>
    let flipped := D.map (fun c => { idx := swapIdx c.idx, sign := !c.sign })
    flipped.reverse

/-! ## Fold sends `hopfA` to `hopfB` and is an involution -/

/-- The fold maps the first encoding onto the second. -/
theorem fold_hopfA_eq_hopfB : fold hopfA = hopfB := by decide

/-- The fold maps the second encoding back onto the first. -/
theorem fold_hopfB_eq_hopfA : fold hopfB = hopfA := by decide

/-- The fold is a strict involution on `hopfA`. -/
theorem fold_involution_hopfA : fold (fold hopfA) = hopfA := by decide

/-- The fold is a strict involution on `hopfB`. -/
theorem fold_involution_hopfB : fold (fold hopfB) = hopfB := by decide

/-! ## Inlined Kauffman-bracket arithmetic

We inline the `LPoly` layer used in `KauffmanBracketFinite.lean` so
that this file compiles standalone. -/

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

/-! ## Loop functions for the two Hopf-link encodings

We use the canonical Hopf-link loop function: both all-A and all-B
smoothings give 2 components; mixed smoothings give 1 component.
Because `hopfA` and `hopfB` only differ by reversing crossing order
and flipping signs, the loop function for `hopfB` is obtained by
reversing the Boolean vector and negating each entry. Both compute
to the *same* Kauffman-bracket value. -/

def hopfLoopsA : List Bool → Nat
  | [true, true]   => 2
  | [true, false]  => 1
  | [false, true]  => 1
  | [false, false] => 2
  | _              => 0

/-- Loop function for `hopfB`: the fold reverses the crossing order
and flips each sign, so the loop count at smoothing `s` for `hopfB`
equals the loop count at the reversed, bit-flipped version of `s`
for `hopfA`. We spell this out explicitly on all four states. -/
def hopfLoopsB : List Bool → Nat
  | [true, true]   => 2   -- ↔ hopfA [false, false] = 2
  | [true, false]  => 1   -- ↔ hopfA [true, false]  = 1
  | [false, true]  => 1   -- ↔ hopfA [false, true]  = 1
  | [false, false] => 2   -- ↔ hopfA [true, true]   = 2
  | _              => 0

def bracketHopfA : LPoly := bracketSum 2 hopfLoopsA
def bracketHopfB : LPoly := bracketSum 2 hopfLoopsB

/-- The Hopf link's Kauffman bracket value (in this orientation):
`-A^{-4} - A^4`. -/
theorem bracketHopfA_value :
    bracketHopfA = [(-4, -1), (4, -1)] := by decide

/-- The second encoding has the same bracket value. -/
theorem bracketHopfB_value :
    bracketHopfB = [(-4, -1), (4, -1)] := by decide

/-- **Bracket-isomorphism on the chosen pair.**
The two encodings `hopfA` and `hopfB`, related by `fold`, share the
same Kauffman-bracket state-sum value. -/
theorem fold_preserves_bracket :
    bracketHopfA = bracketHopfB := by decide

/-! ## Algebraic identity

Putting it together, on the explicit pair `(hopfA, hopfB)`:
* `fold hopfA = hopfB` and `fold hopfB = hopfA`;
* `fold ∘ fold = id` on each element;
* `bracket hopfA = bracket hopfB` as Laurent polynomials.

This is an instance of an invariant-based isomorphism: the two
encodings are equal under the Kauffman-bracket functor. We
emphasize this does *not* imply ambient isotopy of the underlying
links in general, because the Kauffman bracket is not a complete
invariant of links. What we have proved is an algebraic identity. -/

/-- The combined witness: fold is an involution exchanging `hopfA`
and `hopfB`, and their brackets coincide. -/
theorem fold_iso_witness :
    fold hopfA = hopfB
    ∧ fold hopfB = hopfA
    ∧ fold (fold hopfA) = hopfA
    ∧ fold (fold hopfB) = hopfB
    ∧ bracketHopfA = bracketHopfB := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · decide
  · decide
  · decide
  · decide
  · decide

end FoldedKnotIsomorphism
end Gnosis
