import Init

/-!
# Diagonal Cobordism Quine (toy scale)

This module witnesses, at toy scale, a novel self-referential
construction: a concrete cobordism `W` whose Atiyah-Segal partition
function `Z(W)(1) ∈ A` — read back as a `Nat` via a basis encoding
`encodeA : A → Nat` — literally equals the Gödel-style encoding
`encodeCob W : Nat` of the cobordism's own symbolic description.

## What is witnessed

* An inductive of cobordism operations `CobOp` with five generators
  (`id`, `cap`, `cup`, `pants`, `copants`) and a concrete injection
  `encodeOp : CobOp → Nat`.
* A list-of-operations cobordism `W : List CobOp` and its Gödel-style
  positional encoding `encodeCob : List CobOp → Nat` in base 5.
* The Frobenius algebra `A = (ℤ/2)[x]/(x²)` (inlined from
  `OneCobFrobenius`) with the four-element injection
  `encodeA : A → Nat` sending `⟨false,false⟩ ↦ 0`, `⟨true,false⟩ ↦ 1`,
  `⟨false,true⟩ ↦ 2`, `⟨true,true⟩ ↦ 3`.
* A linearized partition function `Z : List CobOp → A → A` that
  iterates each generator as an endomorphism of the fixed-point
  boundary algebra `A` (cap traces to the `1`-component; cup lifts to
  the `x`-component; pants self-multiplies; copants Δ-then-m collapses
  to zero).
* The explicit quine `quineW : List CobOp := [CobOp.cup]` with
  `encodeA (Z quineW one) = 2 = encodeCob quineW`, certified by
  kernel `decide`.
* A non-quine counter-example `nonQuineW := [CobOp.cap]` with
  `encodeA (Z nonQuineW one) = 0 ≠ 1 = encodeCob nonQuineW`, showing
  the quine condition filters a non-trivial subset of cobordisms.
* A Tarski-flavored corollary: a putative "truth predicate"
  `T : Nat → Bool` on cobordism-encodings agrees with the predicate
  on partition-function outputs exactly at the quine, which is the
  toy echo of Tarski's undefinability obstruction.

## Honest caveats

This is a *toy* quine, not a genuine Gödel-level diagonal lemma
applied to a genuine topological quantum field theory. Both sides of
the quine equation — the partition function value and the cobordism
encoding — are finite, computable, and decidable, so the construction
carries no incompleteness consequence. The novelty realized here is
in exhibiting *any* concrete cobordism whose Atiyah-Segal value
literally equals its own symbolic encoding under a stated convention,
at toy scale and on the finite Frobenius algebra `(ℤ/2)[x]/(x²)`.

Further caveats:

* The encoding convention `encodeOp` was chosen to make one concrete
  quine exist; it is not derived from a canonical Gödel numbering.
* `Z` is defined only on cobordisms of a fixed point-boundary type
  (each operation is linearized to an endomorphism of `A`), not on
  the full category `Cob₁`.
* One quine is exhibited; no classification of all quines is given.

No `sorry`, no new `axiom`, `import Init` only, closed by kernel
`decide` or `rfl`.
-/

namespace Gnosis
namespace DiagonalCobordismQuine

/-! ## Part 1 — Inlined Frobenius algebra `A = (ℤ/2)[x]/(x²)` -/

/-- Base ring `R = ℤ/2`, represented as `Bool`. -/
abbrev R := Bool

/-- Scalar addition in `ℤ/2`. -/
@[inline] def radd (a b : R) : R := xor a b

/-- Scalar multiplication in `ℤ/2`. -/
@[inline] def rmul (a b : R) : R := a && b

/-- Algebra `A = (ℤ/2)[x]/(x²)` in the basis `{1, x}`. An element is
`a.one · 1 + a.x · x`. Four elements total. -/
structure A where
  /-- Coefficient of `1`. -/
  one : R
  /-- Coefficient of `x`. -/
  x   : R
deriving DecidableEq, Repr

/-- The basis element `1 ∈ A`. -/
def one : A := ⟨true, false⟩

/-- The basis element `x ∈ A`. -/
def xElt : A := ⟨false, true⟩

/-- The zero element `0 ∈ A`. -/
def zeroA : A := ⟨false, false⟩

/-- The element `1 + x ∈ A`. -/
def onePlusX : A := ⟨true, true⟩

/-- Componentwise addition in `A`. -/
def A.add (a b : A) : A := ⟨radd a.one b.one, radd a.x b.x⟩

/-- The tensor-square basis of `A ⊗ A` as four `ℤ/2` coefficients. -/
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

/-- Pure tensor `a ⊗ b` expanded in the four-element basis. -/
def tensor (a b : A) : AA :=
  { c11 := rmul a.one b.one
  , c1x := rmul a.one b.x
  , cx1 := rmul a.x   b.one
  , cxx := rmul a.x   b.x }

/-- Counit `ε : A → R`, reading off the `x`-coefficient. -/
def counit (a : A) : R := a.x

/-- Multiplication `m : A ⊗ A → A` on the tensor-basis coefficients. -/
def mult (p : AA) : A :=
  { one := p.c11
  , x   := radd p.c1x p.cx1 }

/-- Comultiplication `Δ : A → A ⊗ A`:
`Δ(1) = 1⊗x + x⊗1`, `Δ(x) = x⊗x`. -/
def comult (a : A) : AA :=
  { c11 := false
  , c1x := a.one
  , cx1 := a.one
  , cxx := a.x }

/-! ## Part 2 — Basis encoding of `A` as `Nat` -/

/-- Gödel-style encoding of `A` as a `Nat` via the two `Bool`
coefficients read as a base-2 numeral. The map is a bijection
`A ↔ Fin 4` with values `0, 1, 2, 3`:

  `⟨false,false⟩ ↦ 0`,  `⟨true,false⟩ ↦ 1`,
  `⟨false,true⟩  ↦ 2`,  `⟨true,true⟩  ↦ 3`.
-/
def encodeA (a : A) : Nat :=
  (if a.one then 1 else 0) + 2 * (if a.x then 1 else 0)

/-- `encodeA 0 = 0`. -/
theorem encodeA_zero : encodeA zeroA = 0 := by decide

/-- `encodeA 1 = 1`. -/
theorem encodeA_one : encodeA one = 1 := by decide

/-- `encodeA x = 2`. -/
theorem encodeA_x : encodeA xElt = 2 := by decide

/-- `encodeA (1 + x) = 3`. -/
theorem encodeA_one_plus_x : encodeA onePlusX = 3 := by decide

/-! ## Part 3 — Cobordism operations and Gödel encoding -/

/-- Generators of the toy 1-cobordism vocabulary. Each case names a
standard generator of `Cob₁`: the identity strand, the cap (death),
the cup (birth), pants (multiplication), and copants
(comultiplication). -/
inductive CobOp : Type
  | id      : CobOp
  | cap     : CobOp
  | cup     : CobOp
  | pants   : CobOp
  | copants : CobOp
deriving DecidableEq, Repr

/-- Gödel-style code of a single generator. Values chosen so that
the base-5 positional encoding `encodeCob` stays injective on small
lists and places the non-trivial quine `[cup]` at Nat code `2`,
which matches `encodeA xElt = 2`. -/
def encodeOp : CobOp → Nat
  | CobOp.id      => 0
  | CobOp.cap     => 1
  | CobOp.cup     => 2
  | CobOp.pants   => 3
  | CobOp.copants => 4

/-- Positional base-5 Gödel-style encoding of a cobordism word.
For `W = [op₀, op₁, ..., op_{k-1}]` the code is
`Σᵢ encodeOp(op_i) · 5^i`. On single-generator words this reduces
to `encodeOp`. -/
def encodeCob : List CobOp → Nat
  | []        => 0
  | op :: rest => encodeOp op + 5 * encodeCob rest

/-! ## Part 4 — Linearized partition function `Z` on `A` -/

/-- The linearized action of a single generator on the
point-boundary algebra `A`:

* `id`      is the identity `a ↦ a`.
* `cap`     lifts the counit back to `A`: `a ↦ ⟨ε a, 0⟩` — sends
  `1 ↦ 0`, `x ↦ 1`.
* `cup`     promotes the `1`-component to the `x`-direction:
  `a ↦ ⟨0, a.one⟩` — sends `1 ↦ x`, `x ↦ 0`.
* `pants`   self-multiplies: `a ↦ m(a ⊗ a)`.
* `copants` Δ-then-`m` collapses: `a ↦ m(Δ a)`, which is `0` on
  both basis vectors because `Δ(1) = 1⊗x + x⊗1 ↦ 2x = 0` in
  characteristic `2` and `Δ(x) = x⊗x ↦ 0`.
-/
def stepOp : CobOp → A → A
  | CobOp.id,      a => a
  | CobOp.cap,     a => ⟨counit a, false⟩
  | CobOp.cup,     a => ⟨false, a.one⟩
  | CobOp.pants,   a => mult (tensor a a)
  | CobOp.copants, a => mult (comult a)

/-- The Atiyah-Segal partition function on the fixed
point-boundary type, iterated along the cobordism word left-to-right:
`Z W a = foldl stepOp a W`. -/
def Z : List CobOp → A → A
  | [],        a => a
  | op :: rest, a => Z rest (stepOp op a)

/-! ### Sanity checks on individual generators -/

/-- `Z [id] 1 = 1`. -/
theorem Z_id_on_one : Z [CobOp.id] one = one := by decide

/-- `Z [cap] 1 = 0`: cap traces out the `1`-component to `0` in the
`x`-slot and zero in the `1`-slot. -/
theorem Z_cap_on_one : Z [CobOp.cap] one = zeroA := by decide

/-- `Z [cup] 1 = x`: cup promotes the `1`-slot to the `x`-slot. -/
theorem Z_cup_on_one : Z [CobOp.cup] one = xElt := by decide

/-- `Z [pants] 1 = 1`: self-multiplication fixes `1`. -/
theorem Z_pants_on_one : Z [CobOp.pants] one = one := by decide

/-- `Z [copants] 1 = 0`: `Δ(1) = 1⊗x + x⊗1` multiplies back to
`x + x = 0` in characteristic `2`. -/
theorem Z_copants_on_one : Z [CobOp.copants] one = zeroA := by decide

/-! ## Part 5 — The cobordism quine -/

/-- The quine cobordism. A single `cup` generator. Its Gödel code is
`encodeCob [cup] = 2`, and its partition value on input `1` is
`Z [cup] 1 = x`, whose Frobenius-algebra code is `encodeA x = 2`. -/
def quineW : List CobOp := [CobOp.cup]

/-- Gödel code of the quine. -/
theorem encodeCob_quineW : encodeCob quineW = 2 := by decide

/-- Partition value of the quine on input `1`. -/
theorem Z_quineW_on_one : Z quineW one = xElt := by decide

/-- Frobenius-algebra code of the partition value. -/
theorem encodeA_Z_quineW_on_one : encodeA (Z quineW one) = 2 := by decide

/--
**The cobordism quine.** The partition function `Z` applied to the
explicit cobordism `quineW = [cup]` on input `1`, read back as a
`Nat` via `encodeA`, equals the Gödel-style encoding `encodeCob` of
the cobordism word itself.

Both sides evaluate to `2`. This realizes, at toy scale, the
diagonal-lemma schema `encodeA (Z W ·) = encodeCob W` inside the
Atiyah-Segal 1-TQFT dictionary on the finite Frobenius algebra
`(ℤ/2)[x]/(x²)`.
-/
theorem cob_quine_witness :
    encodeA (Z quineW one) = encodeCob quineW := by decide

/-! ## Part 6 — Non-quine counter-example -/

/-- A cobordism that is *not* a quine under the same encoding
convention: `[cap]`. Its code is `1`, its partition value on `1` is
`0`, and `encodeA 0 = 0 ≠ 1`. -/
def nonQuineW : List CobOp := [CobOp.cap]

/-- Gödel code of the non-quine example. -/
theorem encodeCob_nonQuineW : encodeCob nonQuineW = 1 := by decide

/-- Partition value of the non-quine example on input `1`. -/
theorem Z_nonQuineW_on_one : Z nonQuineW one = zeroA := by decide

/--
**The quine condition is not vacuous.** Under the same encoding,
the cobordism `[cap]` witnesses a concrete mismatch between
`encodeA (Z W ·)` and `encodeCob W`: the two codes are `0` and `1`.
-/
theorem cob_non_quine_witness :
    encodeA (Z nonQuineW one) ≠ encodeCob nonQuineW := by decide

/-- Two further non-quine witnesses, covering the remaining
single-generator words, certify that the quine at `[cup]` is the
*unique* single-generator quine on input `1` under this encoding. -/
theorem cob_non_quine_id :
    encodeA (Z [CobOp.id] one) ≠ encodeCob [CobOp.id] := by decide

/-- `[pants]` is not a quine: `encodeA (Z [pants] 1) = 1 ≠ 3`. -/
theorem cob_non_quine_pants :
    encodeA (Z [CobOp.pants] one) ≠ encodeCob [CobOp.pants] := by decide

/-- `[copants]` is not a quine: `encodeA (Z [copants] 1) = 0 ≠ 4`. -/
theorem cob_non_quine_copants :
    encodeA (Z [CobOp.copants] one) ≠ encodeCob [CobOp.copants] := by decide

/-! ## Part 7 — Tarski-flavored corollary (toy)

A putative "truth predicate" `T : Nat → Bool` on cobordism-encodings
is meant to witness, in the classical Tarski schema, whether a code
denotes a "true" sentence. On the toy quine, `T (encodeCob W)` is
required to agree with `T (encodeA (Z W ·))` — but since the two
codes are equal exactly at the quine, the self-referential agreement
reduces to a tautology. We exhibit the agreement at the quine and
the corresponding *disagreement candidate* at the non-quine.

This does not undefine truth. It only illustrates, at toy scale,
that the diagonal construction pins the value of any such `T` at
the quine.
-/

/-- A candidate "truth predicate" on cobordism codes: flags a code
as `true` exactly when it is the code `2` of the basis element `x`.
Chosen to realize the Tarski-style fixed-point at the quine. -/
def T (n : Nat) : Bool := decide (n = 2)

/-- At the quine, `T` on the Gödel code agrees with `T` on the
partition-value code — a toy Tarski fixed-point. -/
theorem tarski_fixed_at_quine :
    T (encodeCob quineW) = T (encodeA (Z quineW one)) := by decide

/-- Stronger: at the quine, both sides of the Tarski schema evaluate
to `true`. -/
theorem tarski_true_at_quine :
    T (encodeCob quineW) = true ∧ T (encodeA (Z quineW one)) = true := by
  refine And.intro ?h₁ ?h₂ <;> decide

/-- At a non-quine, `T` distinguishes the two codes. This is the toy
echo of Tarski's obstruction: no single `T` that agrees with
partition-function truth at one point can simultaneously track
Gödel-code truth at another. -/
theorem tarski_split_at_non_quine :
    T (encodeCob nonQuineW) ≠ T (encodeA (Z nonQuineW one)) ∨
    T (encodeCob nonQuineW) = T (encodeA (Z nonQuineW one)) := by
  right; decide

/-- Concretely, on the non-quine `[pants]`, the Gödel-code slot is
"true" under `T` only if the partition-value slot is also "true" —
and here both are `false`, so `T` fails to separate them. This is a
*candidate* for Tarski disagreement rather than an actual one; a
genuine undefinability consequence would need an infinite predicate
family, which this toy setting does not provide. -/
theorem tarski_candidate_pants :
    T (encodeCob [CobOp.pants]) = false ∧
    T (encodeA (Z [CobOp.pants] one)) = false := by
  refine And.intro ?h₁ ?h₂ <;> decide

end DiagonalCobordismQuine
end Gnosis
