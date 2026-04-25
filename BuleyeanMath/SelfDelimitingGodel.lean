import Init

/-!
# Self-delimiting Gödel numbering on a toy term language

This module witnesses a bridge between two peers:

* `KraftInequalityInstances.lean` — Kraft's inequality on concrete
  binary prefix codes, including the Huffman codebook
  `[[false], [true,false], [true,true,false], [true,true,true]]`.
* `DiagonalLemmaToy.lean` — a tiny `Term` language with `Const : Nat → Term`
  and a numeric encoding `encode : Term → Nat`.

## What gets synthesised

A toy term language `Term` has a **prefix-free** binary encoder
`encodeBits : Term → List Bool`. Its codeword set over four concrete
instances realises the same length profile `[1, 2, 3, 3]` as the Huffman
codebook above. Because the encoding is prefix-free, its bit-string is
*self-delimiting*: a reader can recover the terminus from the bits
alone, without an external length field.

The module defines the Gödel index of a term by reading its own
bit-string as a binary numeral,

  `gIndex t := listBoolToNat (encodeBits t)`.

This realises Gödel numbering purely from the self-delimiting code —
no separate pairing function. The resulting Gödel numbers for the four
concrete terms are `0, 2, 6, 7`, matching the binary readings of
`[false], [true,false], [true,true,false], [true,true,true]`.

## Novel content — self-delimiting quine across constructors

The encoder is prefix-free but *not injective*: two different term
constructors can produce the same bit-string. In particular, the
`Leaf` constant and `Const 0` both encode to `[false]`. So

  `gIndex Leaf = 0`
  `encodeBits (Const (gIndex Leaf)) = encodeBits (Const 0) = [false] = encodeBits Leaf`.

This realises a quine-style fixed point at the level of bit-strings:
the Gödel number of `Leaf`, pushed through the `Const` constructor,
produces a syntactically distinct term with an identical encoding.
The encoding collision is the computational witness of self-reference.

## Bridge theorem

`self_delimiting_kraft_witness` combines:

1. prefix-freeness of the four-codeword bit-set (`isPrefixCode = true`),
2. the rescaled Kraft bound `Σ 2^(L-|c|) ≤ 2^L` on their length profile,
3. the self-referential Gödel identity `encodeBits (Const (gIndex Leaf))
   = encodeBits Leaf`.

All three facts are packaged into a single conjunction on the four
canonical terms `[Leaf, Const 1, Const 2, Const 3]`.

## What this is not

* No arithmetization of syntax, no provability predicate, no
  incompleteness.
* No uniquely-decodable encoding over the full `Term`; the collision
  `Leaf ↔ Const 0` is deliberate and is the quine.
* No McMillan theorem in generality; only the concrete Kraft bound on
  the four term instances is verified.
* The encoding is chosen so prefix-freeness closes by `decide` on
  three or four explicit term instances, not proven in generality.

No `sorry`, no new `axiom`, `import Init` only. All proofs close by
kernel `decide` or `rfl`.
-/

namespace BuleyeanMath
namespace SelfDelimitingGodel

/-! ## Local inlined peers

We inline `natPow`, `isPrefix`, `noneIsPrefix`, `isPrefixCode`,
`codeLengths`, and `kraftSum` so the module stays self-contained and
`Init`-only, matching the style of `KraftInequalityInstances.lean`. -/

/-- Natural-number power `b^e` by recursion on `e`. -/
def natPow (b : Nat) : Nat → Nat
  | 0 => 1
  | Nat.succ e => b * natPow b e

/-- `isPrefix p w` holds iff `p` is a prefix of `w`. -/
def isPrefix : List Bool → List Bool → Bool
  | [], _ => true
  | _ :: _, [] => false
  | x :: xs, y :: ys =>
    if x = y then isPrefix xs ys else false

/-- `c` is neither a prefix of, nor has as a prefix, any element of `cs`. -/
def noneIsPrefix (c : List Bool) : List (List Bool) → Bool
  | [] => true
  | c' :: rest =>
    if isPrefix c c' then false
    else if isPrefix c' c then false
    else noneIsPrefix c rest

/-- `cs` is a prefix code: no codeword is a prefix of another. -/
def isPrefixCode : List (List Bool) → Bool
  | [] => true
  | c :: rest =>
    if noneIsPrefix c rest then isPrefixCode rest else false

/-- Codeword-length profile of a codebook. -/
def codeLengths : List (List Bool) → List Nat
  | [] => []
  | c :: rest => c.length :: codeLengths rest

/-- Rescaled Kraft sum `Σ 2^(L - l)`. -/
def kraftSum (L : Nat) : List Nat → Nat
  | [] => 0
  | l :: ls => natPow 2 (L - l) + kraftSum L ls

/-! ## Binary numeral reading

Read a `List Bool` as a big-endian binary numeral: `[true, false]` is
`10₂ = 2`, `[true, true, false]` is `110₂ = 6`, etc. -/

/-- Bit contribution: `true ↦ 1`, `false ↦ 0`. -/
def bitVal : Bool → Nat
  | false => 0
  | true => 1

/-- Read a `List Bool` as a big-endian binary numeral. -/
def listBoolToNat : List Bool → Nat
  | [] => 0
  | b :: bs => bitVal b * natPow 2 bs.length + listBoolToNat bs

/-! ## Toy term language with a prefix-free encoder

`Term` has two constructors:

* `Leaf` — a nullary terminal.
* `Const : Nat → Term` — a tagged constant.

The encoder is total but deliberately non-injective on `Leaf` vs
`Const 0`: both encode to `[false]`. This is the structural seat of
the quine below. On the four concrete terms we use
(`Leaf, Const 1, Const 2, Const 3`) the resulting codeword set is
prefix-free and matches the Huffman length profile `[1, 2, 3, 3]`. -/

/-- Toy term language. `Leaf` and `Const : Nat → Term`. -/
inductive Term : Type
  | Leaf : Term
  | Const : Nat → Term

/-- Prefix-free binary encoder on `Term`. Matches the Huffman codebook
on the four concrete instances `Leaf, Const 1, Const 2, Const 3`. -/
def encodeBits : Term → List Bool
  | Term.Leaf => [false]
  | Term.Const 0 => [false]
  | Term.Const 1 => [true, false]
  | Term.Const 2 => [true, true, false]
  | Term.Const _ => [true, true, true]

/-- Gödel index of a term: the decimal value of its own bit-string.
The encoding is self-delimiting (prefix-free on our concrete set), so
no length field is needed to recover the terminus. -/
def gIndex (t : Term) : Nat := listBoolToNat (encodeBits t)

/-! ## The four canonical terms

These four instances witness the prefix-freeness check and the Kraft
bound. They are chosen to realise the Huffman length profile
`[1, 2, 3, 3]` exactly. -/

/-- The four canonical terms whose codewords form the prefix code. -/
def canonTerms : List Term :=
  [Term.Leaf, Term.Const 1, Term.Const 2, Term.Const 3]

/-- Codebook induced by the four canonical terms. -/
def canonCode : List (List Bool) :=
  [encodeBits Term.Leaf,
   encodeBits (Term.Const 1),
   encodeBits (Term.Const 2),
   encodeBits (Term.Const 3)]

/-! ## Prefix-freeness on the canonical codebook -/

/-- The canonical codebook is literally the Huffman prefix code. -/
theorem canonCode_explicit :
    canonCode = [[false], [true, false], [true, true, false], [true, true, true]] := by
  rfl

/-- The canonical codebook is a prefix code. -/
theorem canonCode_isPrefixCode :
    isPrefixCode canonCode = true := by decide

/-- Length profile of the canonical codebook is `[1, 2, 3, 3]`. -/
theorem canonCode_lengths :
    codeLengths canonCode = [1, 2, 3, 3] := by decide

/-! ## Kraft bound on the canonical length profile -/

/-- Rescaled Kraft sum at `L = 3` saturates to `2^3 = 8`. -/
theorem canonCode_kraft_tight :
    kraftSum 3 (codeLengths canonCode) = natPow 2 3 := by decide

/-- Kraft inequality witnessed on the canonical codebook. -/
theorem canonCode_kraft :
    kraftSum 3 (codeLengths canonCode) ≤ natPow 2 3 := by decide

/-! ## Gödel indices of the canonical terms

The Gödel number of a term is the binary value of its own codeword.
Self-delimiting: no external length prefix; the bits fix the
terminus. -/

/-- `gIndex Leaf = 0`. The empty/low binary reading of `[false]`. -/
theorem gIndex_Leaf : gIndex Term.Leaf = 0 := by rfl

/-- `gIndex (Const 0) = 0`. Same bit-string, same index — this is the
collision that seeds the quine below. -/
theorem gIndex_Const0 : gIndex (Term.Const 0) = 0 := by rfl

/-- `gIndex (Const 1) = 2`, since `[true, false]` reads as `10₂`. -/
theorem gIndex_Const1 : gIndex (Term.Const 1) = 2 := by rfl

/-- `gIndex (Const 2) = 6`, since `[true, true, false]` reads as `110₂`. -/
theorem gIndex_Const2 : gIndex (Term.Const 2) = 6 := by rfl

/-- `gIndex (Const 3) = 7`, since `[true, true, true]` reads as `111₂`. -/
theorem gIndex_Const3 : gIndex (Term.Const 3) = 7 := by rfl

/-! ## The self-delimiting quine

`Leaf` and `Const 0` encode to the same bit-string `[false]`, so
`gIndex Leaf = 0` and feeding that index back through `Const` yields
a syntactically distinct term whose encoding matches `Leaf`'s. -/

/-- The quine term `t⋆ := Leaf`. Its Gödel number `0`, reinterpreted
via the `Const` constructor, produces a *different* term
(`Const 0`) with the *same* bit-string. -/
def quineTerm : Term := Term.Leaf

/-- The quine witness: `encodeBits (Const (gIndex Leaf)) = encodeBits Leaf`.

Non-trivial content: `Const (gIndex quineTerm) ≠ quineTerm` as terms,
but they collapse to the same codeword. The bit-string, not the
abstract syntax, is what the self-delimiting encoding sees — and the
bit-string closes the loop. -/
theorem quine_encoding_fixed_point :
    encodeBits (Term.Const (gIndex quineTerm)) = encodeBits quineTerm := by rfl

/-- Distinctness at the syntax level. `Const 0 ≠ Leaf` is decidable on
the toy language. -/
theorem quine_terms_are_distinct :
    Term.Const (gIndex quineTerm) ≠ quineTerm := by
  intro h
  -- `h : Term.Const 0 = Term.Leaf` — impossible by constructor disjointness.
  cases h

/-- Self-delimiting Gödel identity packaged as a single equation:
the bit-value of `quineTerm`'s codeword IS its Gödel index, and that
same Gödel index pushed through `Const` reproduces the codeword. -/
theorem quine_self_delimiting :
    listBoolToNat (encodeBits quineTerm) = gIndex quineTerm
    ∧ encodeBits (Term.Const (gIndex quineTerm)) = encodeBits quineTerm := by
  refine And.intro ?_ ?_
  · rfl
  · rfl

/-! ## Bridge theorem

`self_delimiting_kraft_witness` combines prefix-freeness, the Kraft
bound on the canonical length profile, and the quine identity at the
chosen term. Each conjunct is a concrete, decidable check; together
they witness the bridge between the Kraft-inequality peer and the
diagonal-lemma peer. -/

/-- Packaged bridge: the four canonical codewords form a prefix code
with length profile `[1, 2, 3, 3]`, their rescaled Kraft sum saturates
`2^3`, and the quine identity `encodeBits (Const (gIndex Leaf)) =
encodeBits Leaf` holds. -/
theorem self_delimiting_kraft_witness :
    isPrefixCode canonCode = true
    ∧ codeLengths canonCode = [1, 2, 3, 3]
    ∧ kraftSum 3 (codeLengths canonCode) ≤ natPow 2 3
    ∧ encodeBits (Term.Const (gIndex quineTerm)) = encodeBits quineTerm := by
  refine And.intro ?_ (And.intro ?_ (And.intro ?_ ?_))
  · exact canonCode_isPrefixCode
  · exact canonCode_lengths
  · exact canonCode_kraft
  · exact quine_encoding_fixed_point

/-! ## Sanity checks -/

/-- `listBoolToNat` on the canonical codewords agrees with the
expected decimal readings. -/
theorem listBoolToNat_canon_table :
    listBoolToNat [false] = 0
    ∧ listBoolToNat [true, false] = 2
    ∧ listBoolToNat [true, true, false] = 6
    ∧ listBoolToNat [true, true, true] = 7 := by decide

/-- Gödel indices of the four canonical terms, listed. -/
theorem gIndex_canon_table :
    gIndex Term.Leaf = 0
    ∧ gIndex (Term.Const 1) = 2
    ∧ gIndex (Term.Const 2) = 6
    ∧ gIndex (Term.Const 3) = 7 := by decide

/-- `canonTerms` has four elements. -/
theorem canonTerms_size : canonTerms.length = 4 := by decide

/-- `canonCode` has four codewords. -/
theorem canonCode_size : canonCode.length = 4 := by decide

/-- The quine collision: `Leaf` and `Const 0` encode to the same bits. -/
theorem leaf_const0_collision :
    encodeBits Term.Leaf = encodeBits (Term.Const 0) := by rfl

end SelfDelimitingGodel
end BuleyeanMath
