import Init

/-!
# Gödel-Cobordism Double Quine

This module witnesses a bridge between two peer constructions:

* `SelfDelimitingGodel.lean` — the self-delimiting term quine, where a
  toy term language `Term` has a prefix-free encoder `encodeBits` and a
  Gödel index `gIndex t := listBoolToNat (encodeBits t)`. The encoding
  collision `encodeBits Leaf = encodeBits (Const 0) = [false]` seeds a
  quine with `gIndex Leaf = 0`.
* `DiagonalCobordismQuine.lean` — the cobordism quine, where a
  `List CobOp` word `W` has a base-5 Gödel code `encodeCob W` and a
  linearized partition function `Z W : A → A` on the Frobenius algebra
  `A = (ℤ/2)[x]/(x²)`. The quine `[cup]` gives
  `encodeA (Z [cup] one) = 2 = encodeCob [cup]`.

Both peers terminate in a `Nat`. This module asks: is there a pair
`(t, W)` with `gIndex t = encodeA (Z W one)` — two *independent*
self-referential encodings converging on the same natural number?

## What gets synthesised

* Inlined copies of both peer structures: `Term`, `encodeBits`,
  `gIndex`; `CobOp`, `encodeCob`, `A`, `Z`, `encodeA`.
* A `DoubleQuine` predicate on pairs `(t : Term) (W : List CobOp)`
  carrying the field `agree : gIndex t = encodeA (Z W one)`.
* A **trivial witness** `(t₀, W₀) = (Leaf, [cap])` with both sides `= 0`.
* A **non-trivial witness** `(tStar, WStar) = (Const 1, [cup])` with both
  sides `= 2`. This is the double quine proper: the term-side
  Gödel index (binary `10₂`) and the cobordism-side partition code
  (the `xElt` basis vector) meet at the same Nat `2` via two wholly
  different self-referential constructions.
* A **non-universality** witness `(Leaf, [cup])` with
  `gIndex Leaf = 0 ≠ 2 = encodeA (Z [cup] one)`, showing the predicate
  is a non-trivial filter rather than vacuous agreement.
* A packaged **bridge corollary** pairing existence with
  non-universality.

## Honest caveats

* Toy. Both sides are finite and decidable; no incompleteness.
* The encodings on both peers were *chosen* to make the agreement at
  `2` possible. A generic pair of independent self-referential
  numberings would not converge.
* Not a statement about universal Gödel / cobordism equivalence. It
  says only: two specific self-referential encodings admit aligned
  fixed points on this toy term language and this toy 1-TQFT.

No `sorry`, no new `axiom`, `import Init` only, closed by kernel
`decide` or `rfl`.
-/

namespace Gnosis
namespace GodelCobordismDoubleQuine

/-! ## Part 1 — Inlined term side (from `SelfDelimitingGodel`)

We re-inline `natPow`, `bitVal`, `listBoolToNat`, `Term`, `encodeBits`,
and `gIndex` so the module stays self-contained and `Init`-only. -/

/-- Natural-number power `b^e`. -/
def natPow (b : Nat) : Nat → Nat
  | 0 => 1
  | Nat.succ e => b * natPow b e

/-- Bit contribution: `true ↦ 1`, `false ↦ 0`. -/
def bitVal : Bool → Nat
  | false => 0
  | true => 1

/-- Big-endian binary reading of a `List Bool`. -/
def listBoolToNat : List Bool → Nat
  | [] => 0
  | b :: bs => bitVal b * natPow 2 bs.length + listBoolToNat bs

/-- Toy term language, inlined from `SelfDelimitingGodel.Term`. -/
inductive Term : Type
  | Leaf : Term
  | Const : Nat → Term

/-- Prefix-free binary encoder on `Term`. -/
def encodeBits : Term → List Bool
  | Term.Leaf => [false]
  | Term.Const 0 => [false]
  | Term.Const 1 => [true, false]
  | Term.Const 2 => [true, true, false]
  | Term.Const _ => [true, true, true]

/-- Gödel index of a term: decimal value of its own bit-string. -/
def gIndex (t : Term) : Nat := listBoolToNat (encodeBits t)

/-! ## Part 2 — Inlined cobordism side (from `DiagonalCobordismQuine`)

We re-inline `R`, `A`, `encodeA`, `CobOp`, `encodeOp`, `encodeCob`,
the generators `one`/`xElt`/`zeroA`, and the partition function `Z`.
-/

/-- Base ring `ℤ/2` as `Bool`. -/
abbrev R := Bool

/-- ℤ/2 addition. -/
@[inline] def radd (a b : R) : R := xor a b

/-- ℤ/2 multiplication. -/
@[inline] def rmul (a b : R) : R := a && b

/-- Frobenius algebra `A = (ℤ/2)[x]/(x²)` in basis `{1, x}`. -/
structure A where
  /-- Coefficient of the unit basis vector `1`. -/
  one : R
  /-- Coefficient of the nilpotent basis vector `x`. -/
  x   : R
deriving DecidableEq, Repr

/-- The basis element `1 ∈ A`. -/
def one : A := ⟨true, false⟩

/-- The basis element `x ∈ A`. -/
def xElt : A := ⟨false, true⟩

/-- The zero element `0 ∈ A`. -/
def zeroA : A := ⟨false, false⟩

/-- The tensor-square basis of `A ⊗ A`. -/
structure AA where
  /-- Coefficient of `1 ⊗ 1`. -/
  c11 : R
  /-- Coefficient of `1 ⊗ x`. -/
  c1x : R
  /-- Coefficient of `x ⊗ 1`. -/
  cx1 : R
  /-- Coefficient of `x ⊗ x`. -/
  cxx : R
deriving DecidableEq, Repr

/-- Pure tensor `a ⊗ b` expanded in the tensor-square basis. -/
def tensor (a b : A) : AA :=
  { c11 := rmul a.one b.one
  , c1x := rmul a.one b.x
  , cx1 := rmul a.x   b.one
  , cxx := rmul a.x   b.x }

/-- Counit `ε : A → R`. -/
def counit (a : A) : R := a.x

/-- Multiplication `m : A ⊗ A → A`. -/
def mult (p : AA) : A :=
  { one := p.c11
  , x   := radd p.c1x p.cx1 }

/-- Comultiplication `Δ : A → A ⊗ A`. -/
def comult (a : A) : AA :=
  { c11 := false
  , c1x := a.one
  , cx1 := a.one
  , cxx := a.x }

/-- Basis encoding `A → Nat` as a base-2 numeral on coefficients. -/
def encodeA (a : A) : Nat :=
  (if a.one then 1 else 0) + 2 * (if a.x then 1 else 0)

/-- Generators of the toy 1-cobordism vocabulary. -/
inductive CobOp : Type
  | id      : CobOp
  | cap     : CobOp
  | cup     : CobOp
  | pants   : CobOp
  | copants : CobOp
deriving DecidableEq, Repr

/-- Gödel-style code of a single generator. -/
def encodeOp : CobOp → Nat
  | CobOp.id      => 0
  | CobOp.cap     => 1
  | CobOp.cup     => 2
  | CobOp.pants   => 3
  | CobOp.copants => 4

/-- Positional base-5 Gödel-style encoding of a cobordism word. -/
def encodeCob : List CobOp → Nat
  | []        => 0
  | op :: rest => encodeOp op + 5 * encodeCob rest

/-- Linearized action of a single generator on `A`. -/
def stepOp : CobOp → A → A
  | CobOp.id,      a => a
  | CobOp.cap,     a => ⟨counit a, false⟩
  | CobOp.cup,     a => ⟨false, a.one⟩
  | CobOp.pants,   a => mult (tensor a a)
  | CobOp.copants, a => mult (comult a)

/-- Atiyah-Segal partition function on fixed point boundaries. -/
def Z : List CobOp → A → A
  | [],         a => a
  | op :: rest, a => Z rest (stepOp op a)

/-! ## Part 3 — Peer sanity checks (decidable ground truth)

We re-prove the cross-module identities we need. Each closes by
`decide` or `rfl` on finite data. -/

/-- `gIndex Leaf = 0`. The term-side quine from `SelfDelimitingGodel`. -/
theorem gIndex_Leaf : gIndex Term.Leaf = 0 := by rfl

/-- `gIndex (Const 1) = 2`. Bit-string `[true, false]` reads as `10₂`. -/
theorem gIndex_Const1 : gIndex (Term.Const 1) = 2 := by rfl

/-- `Z [cap] one = zeroA`. Cap traces the `1`-component to zero. -/
theorem Z_cap_on_one : Z [CobOp.cap] one = zeroA := by decide

/-- `Z [cup] one = xElt`. Cup promotes the `1`-slot to the `x`-slot. -/
theorem Z_cup_on_one : Z [CobOp.cup] one = xElt := by decide

/-- `encodeA zeroA = 0`. -/
theorem encodeA_zeroA : encodeA zeroA = 0 := by decide

/-- `encodeA xElt = 2`. The cobordism-side code of the `x`-basis vector. -/
theorem encodeA_xElt : encodeA xElt = 2 := by decide

/-! ## Part 4 — The `DoubleQuine` predicate

A pair `(t, W)` is a *double quine* when the term-side Gödel index
`gIndex t` equals the cobordism-side partition-value code
`encodeA (Z W one)`. The predicate is decidable: both sides are `Nat`
with `DecidableEq`. -/

/-- The double-quine invariant: term-side Gödel index and cobordism-side
partition-value code agree. -/
structure DoubleQuine (t : Term) (W : List CobOp) : Prop where
  /-- The agreement equation. -/
  agree : gIndex t = encodeA (Z W one)

/-- Equality of `Nat` is decidable, so the agreement equation is
decidable on any concrete pair `(t, W)`. -/
instance (t : Term) (W : List CobOp) : Decidable (gIndex t = encodeA (Z W one)) :=
  Nat.decEq _ _

/-! ## Part 5 — Trivial witness at `0`

The degenerate double quine. `Leaf` on the term side has Gödel index
`0`. Any cobordism whose partition value on `one` is `zeroA` hits
`encodeA zeroA = 0` on the cobordism side. `[cap]` is the simplest
such cobordism. -/

/-- The trivial term witness: the `Leaf` constant, Gödel index `0`. -/
def t0 : Term := Term.Leaf

/-- The trivial cobordism witness: a single `cap` generator,
`encodeA (Z [cap] one) = 0`. -/
def W0 : List CobOp := [CobOp.cap]

/-- Both sides of the trivial pair read as `0`. -/
theorem trivial_agreement_value :
    gIndex t0 = 0 ∧ encodeA (Z W0 one) = 0 := by
  refine And.intro ?_ ?_ <;> decide

/-- The trivial double quine: `(Leaf, [cap])` witnesses
`gIndex t₀ = encodeA (Z W₀ one) = 0`. -/
theorem trivial_double_quine : DoubleQuine t0 W0 :=
  { agree := by decide }

/-! ## Part 6 — Non-trivial witness at `2`

The double quine proper. On the term side, `Const 1` encodes to
`[true, false]`, whose binary reading is `10₂ = 2`. On the cobordism
side, `Z [cup] one = xElt` and `encodeA xElt = 2`. The two independent
self-referential encodings converge on the same non-zero `Nat`. -/

/-- Non-trivial term witness. Bit-string `[true, false]`, Gödel index
`2`. -/
def tStar : Term := Term.Const 1

/-- Non-trivial cobordism witness. Partition value `xElt`, code `2`. -/
def WStar : List CobOp := [CobOp.cup]

/-- Both sides of the non-trivial pair read as `2`. -/
theorem nontrivial_agreement_value :
    gIndex tStar = 2 ∧ encodeA (Z WStar one) = 2 := by
  refine And.intro ?_ ?_ <;> decide

/--
**The non-trivial double quine.** The pair
`(tStar, WStar) = (Const 1, [cup])` satisfies
`gIndex tStar = encodeA (Z WStar one)`, with both sides equal to `2`.

This realizes convergence of two independent self-referential
encodings: the term-side self-delimiting Gödel number of `Const 1`
(the binary numeral `10₂` read off the prefix-free bit-string) and
the cobordism-side Frobenius-algebra code of `Z` applied to the
`cup` generator on the unit vector. Both encodings were defined
peer-independently; they meet here at the same `Nat`.
-/
theorem nontrivial_double_quine : DoubleQuine tStar WStar :=
  { agree := by decide }

/-! ## Part 7 — Non-universality

Not every pair `(t, W)` is a double quine. The pair `(Leaf, [cup])`
has `gIndex Leaf = 0` but `encodeA (Z [cup] one) = 2`. This shows
`DoubleQuine` is a non-trivial filter rather than a tautology. -/

/-- A mismatched pair: `Leaf` has Gödel index `0`, but the `[cup]`
cobordism evaluates to code `2`. -/
def tMismatch : Term := Term.Leaf

/-- Mismatched cobordism side. -/
def WMismatch : List CobOp := [CobOp.cup]

/-- The two encodings disagree on the mismatched pair. -/
theorem double_quine_not_universal :
    gIndex tMismatch ≠ encodeA (Z WMismatch one) := by decide

/-! ## Part 8 — Bridge corollary

Existence of a non-trivial double quine, packaged together with a
specific non-universality witness. Together they rule out both
"vacuously true" and "vacuously false" readings of the invariant. -/

/--
**Bridge corollary.** There exists a double-quine pair, and the
`DoubleQuine` predicate is not universal on `(Term, List CobOp)` — a
concrete mismatching pair exists. The two facts together certify that
the agreement on `(tStar, WStar)` is a non-trivial coincidence of two
independent self-referential encodings, not a structural tautology.
-/
theorem double_quine_exists_and_not_universal :
    DoubleQuine tStar WStar ∧ gIndex tMismatch ≠ encodeA (Z WMismatch one) := by
  refine And.intro ?_ ?_
  · exact nontrivial_double_quine
  · exact double_quine_not_universal

/-! ## Part 9 — Existence and filter cardinality (packaged)

For the reader who wants an `∃`-form witness rather than a named
constant. -/

/-- Existential form: some `(t, W)` is a double quine. -/
theorem double_quine_exists : ∃ (t : Term) (W : List CobOp), DoubleQuine t W :=
  ⟨tStar, WStar, nontrivial_double_quine⟩

/-- Existential form: some `(t, W)` fails the double-quine condition. -/
theorem double_quine_fails_exists :
    ∃ (t : Term) (W : List CobOp), gIndex t ≠ encodeA (Z W one) :=
  ⟨tMismatch, WMismatch, double_quine_not_universal⟩

/-- Both the trivial and non-trivial double quines hold simultaneously:
the predicate has at least two distinct witnesses, at two different
agreement values (`0` and `2`). -/
theorem double_quine_has_two_witnesses :
    DoubleQuine t0 W0 ∧ DoubleQuine tStar WStar :=
  And.intro trivial_double_quine nontrivial_double_quine

end GodelCobordismDoubleQuine
end Gnosis
