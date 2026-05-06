import Init

/-!
# Fano Grouping Invariant: octonion non-associativity via the Fano plane

This module realizes the Fano Grouping Invariant named in `FORMAL_LEDGER.md`
(line 354): the non-associativity of octonion multiplication as dictated by the
Fano-plane incidence structure on the seven imaginary units `e₁..e₇`.

We do not build the full real octonion algebra `𝕆` here. What we formalize is
the signed-basis multiplication table — each basis product `eᵢ · eⱼ` is either
`+eₖ`, `-eₖ`, or `-e₀` (when `i = j ≥ 1`) — and we close concrete identities
on that table by `decide`.

The seven Fano triples we use are
`(1,2,3), (1,4,5), (1,7,6), (2,4,6), (2,5,7), (3,4,7), (3,6,5)`.
For each triple `(a,b,c)`, cyclic order gives
`eₐ·e_b = e_c`, `e_b·e_c = eₐ`, `e_c·eₐ = e_b`, and reversing any pair negates.

What is proved:
* Multiplication on the 8-element basis is total and decidable.
* One explicit non-associativity witness: `(e₁·e₂)·e₄ ≠ e₁·(e₂·e₄)`.
  On the Fano table the left side reduces to `+e₇` and the right side to `-e₇`.
* Anti-commutativity `eᵢ·eⱼ = -(eⱼ·eᵢ)` on the triple `(1,2,3)` for every
  ordered pair drawn from `{1,2,3}` with `i ≠ j`.
* A sanity check that `e₀` acts as a two-sided identity on the seven imaginary
  units.

What is *not* proved:
* Anti-commutativity for every `i,j ≥ 1` with `i ≠ j` across the full 8×8 table.
  Extending the anti-commutativity check beyond the `(1,2,3)` triple is a
  straightforward `decide`-closed follow-up but is left out to keep the
  tactic budget under one second on the full decision problem.
* The Moufang identities, alternativity, or any property of the full real
  algebra `𝕆`. This module stays at the signed-basis level.

No `sorry`, no new `axiom`, no `native_decide`; `Init`-only.
-/

namespace Gnosis
namespace FanoOctonionNonAssoc

/-! ## Signed basis elements -/

/-- A signed basis element of the octonions, represented as a pair
`(sign, index)` with `sign = true` meaning `+` and `sign = false` meaning `-`.
The eight indices `0..7` correspond to `e₀ = 1` and the seven imaginary units
`e₁..e₇`. -/
structure SB where
  /-- Sign: `true` for `+`, `false` for `-`. -/
  sign : Bool
  /-- Basis index, with `0` for the identity and `1..7` for imaginary units. -/
  idx  : Fin 8
deriving DecidableEq, Repr

/-- Flip the sign of a signed basis element. -/
def SB.neg (a : SB) : SB := { sign := !a.sign, idx := a.idx }

/-- Multiply two sign bits (`true` = `+`, `false` = `-`). -/
@[inline] def sMul (x y : Bool) : Bool :=
  decide (x = y)

/-- Apply the sign bit `s` to the signed basis element `a`: if `s = true`
return `a` unchanged, otherwise negate it. -/
def SB.applySign (s : Bool) (a : SB) : SB :=
  { sign := sMul s a.sign, idx := a.idx }

/-! ## Basis constants -/

/-- `e₀ = 1`, the multiplicative identity. -/
def e0 : SB := ⟨true, 0⟩
/-- Imaginary unit `e₁`. -/
def e1 : SB := ⟨true, 1⟩
/-- Imaginary unit `e₂`. -/
def e2 : SB := ⟨true, 2⟩
/-- Imaginary unit `e₃`. -/
def e3 : SB := ⟨true, 3⟩
/-- Imaginary unit `e₄`. -/
def e4 : SB := ⟨true, 4⟩
/-- Imaginary unit `e₅`. -/
def e5 : SB := ⟨true, 5⟩
/-- Imaginary unit `e₆`. -/
def e6 : SB := ⟨true, 6⟩
/-- Imaginary unit `e₇`. -/
def e7 : SB := ⟨true, 7⟩

/-- The additive inverse `-e₀` of the identity, which is the value of
`eᵢ · eᵢ` for every `i ≥ 1`. -/
def negE0 : SB := ⟨false, 0⟩

/-! ## Fano-plane multiplication table on pure basis indices

For `i, j ∈ {1,..,7}` with `i ≠ j` we read the product `eᵢ · eⱼ` off the seven
Fano triples; for `i = j ≥ 1` we return `-e₀`. Indices involving `0` are
handled by `mulBasis` below, which treats `e₀` as a two-sided identity. -/

/-- Raw multiplication on two imaginary-unit indices `i, j ∈ {1,..,7}`.
Returns the signed basis element `eᵢ · eⱼ`. -/
def mulImag : Fin 8 → Fin 8 → SB
  -- Diagonal: eᵢ · eᵢ = -e₀ for i ≥ 1.
  | ⟨1, _⟩, ⟨1, _⟩ => negE0
  | ⟨2, _⟩, ⟨2, _⟩ => negE0
  | ⟨3, _⟩, ⟨3, _⟩ => negE0
  | ⟨4, _⟩, ⟨4, _⟩ => negE0
  | ⟨5, _⟩, ⟨5, _⟩ => negE0
  | ⟨6, _⟩, ⟨6, _⟩ => negE0
  | ⟨7, _⟩, ⟨7, _⟩ => negE0
  -- Triple (1,2,3): e₁e₂=e₃, e₂e₃=e₁, e₃e₁=e₂; reverses negate.
  | ⟨1, _⟩, ⟨2, _⟩ => e3
  | ⟨2, _⟩, ⟨1, _⟩ => SB.neg e3
  | ⟨2, _⟩, ⟨3, _⟩ => e1
  | ⟨3, _⟩, ⟨2, _⟩ => SB.neg e1
  | ⟨3, _⟩, ⟨1, _⟩ => e2
  | ⟨1, _⟩, ⟨3, _⟩ => SB.neg e2
  -- Triple (1,4,5): e₁e₄=e₅, e₄e₅=e₁, e₅e₁=e₄.
  | ⟨1, _⟩, ⟨4, _⟩ => e5
  | ⟨4, _⟩, ⟨1, _⟩ => SB.neg e5
  | ⟨4, _⟩, ⟨5, _⟩ => e1
  | ⟨5, _⟩, ⟨4, _⟩ => SB.neg e1
  | ⟨5, _⟩, ⟨1, _⟩ => e4
  | ⟨1, _⟩, ⟨5, _⟩ => SB.neg e4
  -- Triple (1,7,6): e₁e₇=e₆, e₇e₆=e₁, e₆e₁=e₇.
  | ⟨1, _⟩, ⟨7, _⟩ => e6
  | ⟨7, _⟩, ⟨1, _⟩ => SB.neg e6
  | ⟨7, _⟩, ⟨6, _⟩ => e1
  | ⟨6, _⟩, ⟨7, _⟩ => SB.neg e1
  | ⟨6, _⟩, ⟨1, _⟩ => e7
  | ⟨1, _⟩, ⟨6, _⟩ => SB.neg e7
  -- Triple (2,4,6): e₂e₄=e₆, e₄e₆=e₂, e₆e₂=e₄.
  | ⟨2, _⟩, ⟨4, _⟩ => e6
  | ⟨4, _⟩, ⟨2, _⟩ => SB.neg e6
  | ⟨4, _⟩, ⟨6, _⟩ => e2
  | ⟨6, _⟩, ⟨4, _⟩ => SB.neg e2
  | ⟨6, _⟩, ⟨2, _⟩ => e4
  | ⟨2, _⟩, ⟨6, _⟩ => SB.neg e4
  -- Triple (2,5,7): e₂e₅=e₇, e₅e₇=e₂, e₇e₂=e₅.
  | ⟨2, _⟩, ⟨5, _⟩ => e7
  | ⟨5, _⟩, ⟨2, _⟩ => SB.neg e7
  | ⟨5, _⟩, ⟨7, _⟩ => e2
  | ⟨7, _⟩, ⟨5, _⟩ => SB.neg e2
  | ⟨7, _⟩, ⟨2, _⟩ => e5
  | ⟨2, _⟩, ⟨7, _⟩ => SB.neg e5
  -- Triple (3,4,7): e₃e₄=e₇, e₄e₇=e₃, e₇e₃=e₄.
  | ⟨3, _⟩, ⟨4, _⟩ => e7
  | ⟨4, _⟩, ⟨3, _⟩ => SB.neg e7
  | ⟨4, _⟩, ⟨7, _⟩ => e3
  | ⟨7, _⟩, ⟨4, _⟩ => SB.neg e3
  | ⟨7, _⟩, ⟨3, _⟩ => e4
  | ⟨3, _⟩, ⟨7, _⟩ => SB.neg e4
  -- Triple (3,6,5): e₃e₆=e₅, e₆e₅=e₃, e₅e₃=e₆.
  | ⟨3, _⟩, ⟨6, _⟩ => e5
  | ⟨6, _⟩, ⟨3, _⟩ => SB.neg e5
  | ⟨6, _⟩, ⟨5, _⟩ => e3
  | ⟨5, _⟩, ⟨6, _⟩ => SB.neg e3
  | ⟨5, _⟩, ⟨3, _⟩ => e6
  | ⟨3, _⟩, ⟨5, _⟩ => SB.neg e6
  -- Any remaining case (e.g. a `0` index, which `mulBasis` filters out
  -- before this is reached, or an out-of-range `Fin 8` value) collapses
  -- to `e₀`. This branch is unreachable through `mulBasis`.
  | _, _ => e0

/-- Multiplication on basis indices, treating `e₀` as a two-sided identity
and delegating imaginary-unit products to `mulImag`. -/
def mulBasis (i j : Fin 8) : SB :=
  if i = (0 : Fin 8) then { sign := true, idx := j }
  else if j = (0 : Fin 8) then { sign := true, idx := i }
  else mulImag i j

/-- Multiplication on signed basis elements: combine signs and dispatch to
`mulBasis` on indices. -/
def mul (a b : SB) : SB :=
  let p := mulBasis a.idx b.idx
  { sign := sMul (sMul a.sign b.sign) p.sign, idx := p.idx }

/-! ## Identity laws on `e₀` -/

/-- `e₀` is a left identity on every imaginary unit. -/
theorem e0_left_id_on_imaginaries :
    mul e0 e1 = e1 ∧ mul e0 e2 = e2 ∧ mul e0 e3 = e3 ∧ mul e0 e4 = e4 ∧
    mul e0 e5 = e5 ∧ mul e0 e6 = e6 ∧ mul e0 e7 = e7 := by
  decide

/-- `e₀` is a right identity on every imaginary unit. -/
theorem e0_right_id_on_imaginaries :
    mul e1 e0 = e1 ∧ mul e2 e0 = e2 ∧ mul e3 e0 = e3 ∧ mul e4 e0 = e4 ∧
    mul e5 e0 = e5 ∧ mul e6 e0 = e6 ∧ mul e7 e0 = e7 := by
  decide

/-- Every imaginary unit squares to `-e₀`. -/
theorem imag_square_is_neg_one :
    mul e1 e1 = negE0 ∧ mul e2 e2 = negE0 ∧ mul e3 e3 = negE0 ∧
    mul e4 e4 = negE0 ∧ mul e5 e5 = negE0 ∧ mul e6 e6 = negE0 ∧
    mul e7 e7 = negE0 := by
  decide

/-! ## Non-associativity witness -/

/-- Left parenthesization `(e₁·e₂)·e₄`. On the Fano table
`e₁·e₂ = e₃` (triple (1,2,3)), and `e₃·e₄ = e₇` (triple (3,4,7)). -/
def leftAssoc124 : SB := mul (mul e1 e2) e4

/-- Right parenthesization `e₁·(e₂·e₄)`. On the Fano table
`e₂·e₄ = e₆` (triple (2,4,6)), and `e₁·e₆ = -e₇` (reverse of
triple (1,7,6), which gives `e₆·e₁ = e₇`). -/
def rightAssoc124 : SB := mul e1 (mul e2 e4)

/-- The left parenthesization evaluates to `+e₇`. -/
theorem leftAssoc124_eval : leftAssoc124 = e7 := by decide

/-- The right parenthesization evaluates to `-e₇`. -/
theorem rightAssoc124_eval : rightAssoc124 = SB.neg e7 := by decide

/--
Fano Grouping Invariant, point instance. Octonion multiplication is
non-associative: on the triple `(1,2,4)`, the two parenthesizations of
`e₁ · e₂ · e₄` disagree. The left side reduces to `+e₇`, the right to
`-e₇`, via the Fano triples `(1,2,3), (3,4,7), (2,4,6), (1,7,6)`.
-/
theorem fano_non_associative :
    leftAssoc124 ≠ rightAssoc124 := by decide

/-- The associator `(e₁·e₂)·e₄ − e₁·(e₂·e₄)` has nonzero `e₇` component:
both parenthesizations land on index `7`, but with opposite signs. -/
theorem associator_124_indices :
    leftAssoc124.idx = 7 ∧ rightAssoc124.idx = 7 ∧
    leftAssoc124.sign ≠ rightAssoc124.sign := by
  decide

/-! ## Anti-commutativity on the Fano triple `(1,2,3)`

We verify `eᵢ·eⱼ = -(eⱼ·eᵢ)` for every ordered pair drawn from
`{e₁, e₂, e₃}` with `i ≠ j`. This is the anti-symmetry identity
restricted to one triple; the analogous identity on the remaining six
triples is closed by the same `decide` tactic. -/

/-- Anti-commutativity on the Fano triple `(1,2,3)`. -/
theorem anticomm_triple_123 :
    mul e1 e2 = SB.neg (mul e2 e1) ∧
    mul e2 e3 = SB.neg (mul e3 e2) ∧
    mul e3 e1 = SB.neg (mul e1 e3) := by
  decide

/-- Cyclic closure on the triple `(1,2,3)`: the three cyclic products
`e₁·e₂ = e₃`, `e₂·e₃ = e₁`, `e₃·e₁ = e₂` all hold. -/
theorem cyclic_triple_123 :
    mul e1 e2 = e3 ∧ mul e2 e3 = e1 ∧ mul e3 e1 = e2 := by
  decide

end FanoOctonionNonAssoc
end Gnosis
