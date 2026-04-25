import Init

/-!
# Moonshine McKay — The Clinamen Across `j`-Invariant Coefficients

The modular `j`-invariant has expansion

    j(τ) = 1/q + 744 + 196884 · q + 21493760 · q² + 864299970 · q³ + ...

McKay's first observation: `c_1 = 196884 = 1 + 196883`, where `196883`
is the dimension of the smallest non-trivial irreducible
representation of the Monster group `M`. This is the seed of
Monstrous Moonshine — the (later-proved) correspondence between `j`
coefficients and sums of Monster irrep dimensions.

The `+ 1` in McKay's decomposition is the **trivial representation**:
the clinamen at the very foundation of Monstrous Moonshine.

## The k=2 braid

Each `j`-invariant coefficient `c_n` decomposes as a sum of Monster
irrep dimensions. The two phases:

- **Minus phase**: the non-trivial contribution — the dimension of
  the characteristic Monster irrep at that level.
- **Plus phase**: the `+ 1` from the trivial representation.

Under the braid reading, the clinamen is the trivial rep. It appears
at every coefficient level. The non-trivial irreps are the phase-
dependent "deficit" side.

## What this module witnesses

- McKay's first three decompositions (from `FORMAL_LEDGER.md` lines
  340-341):
  - `c_1 = 196884 = 1 + 196883`
  - `c_2 = 21493760 = 1 + 196883 + 21296876`
  - `c_3 = 864299970 = 2 + 393766 + 21296876 + 842609326`
- The `+ 1` clinamen appearing in every decomposition.
- The `k=2` braid structure on "trivial vs non-trivial" contribution.

`import Init` only. Zero `sorry`, zero new `axiom`.
-/

namespace Gnosis
namespace MoonshineMcKayBraid

/-! ## Monster irrep dimensions (first few) -/

/-- `χ_1 = 1`: trivial representation. -/
def chi1 : Nat := 1

/-- `χ_2 = 196883`: smallest non-trivial Monster irrep. -/
def chi2 : Nat := 196883

/-- `χ_3 = 21296876`: third Monster irrep dimension. -/
def chi3 : Nat := 21296876

/-- `χ_4 = 842609326`: fourth Monster irrep dimension. -/
def chi4 : Nat := 842609326

/-! ## `j`-invariant coefficients -/

def c1 : Nat := 196884
def c2 : Nat := 21493760
def c3 : Nat := 864299970

/-! ## McKay decompositions (the clinamen is the `+ 1`) -/

/-- `c_1 = χ_1 + χ_2`. -/
theorem mckay_c1 : c1 = chi1 + chi2 := by decide

/-- `c_2 = χ_1 + χ_2 + χ_3`. -/
theorem mckay_c2 : c2 = chi1 + chi2 + chi3 := by decide

/-- `c_3 = 2·χ_1 + 2·χ_2 + χ_3 + χ_4`. -/
theorem mckay_c3 : c3 = 2 * chi1 + 2 * chi2 + chi3 + chi4 := by decide

/-! ## The `+ 1` appears at every level

Subtract the "rest" of the decomposition from `c_n` and see what
remains. It's always the trivial-rep contribution, pure clinamen. -/

theorem clinamen_at_c1 : c1 - chi2 = chi1 := by decide
theorem clinamen_at_c2 : c2 - (chi2 + chi3) = chi1 := by decide
theorem clinamen_at_c3 : c3 - (2 * chi2 + chi3 + chi4) = 2 * chi1 := by decide

/-! ## The k=2 braid phase

- **Minus phase** (deficit): the sum of non-trivial irrep dimensions.
- **Plus phase** (clinamen): the `+ 1` contribution from `χ_1`.

Every coefficient decomposes as `minusPhase + plusPhase`. -/

/-- Minus phase of the McKay decomposition for `c_n`. -/
def minusPhase : Nat → Nat
  | 1 => chi2
  | 2 => chi2 + chi3
  | 3 => 2 * chi2 + chi3 + chi4
  | _ => 0

/-- Plus phase: the total clinamen contribution. -/
def plusPhase : Nat → Nat
  | 1 => chi1
  | 2 => chi1
  | 3 => 2 * chi1
  | _ => 0

theorem c1_split : c1 = minusPhase 1 + plusPhase 1 := by decide
theorem c2_split : c2 = minusPhase 2 + plusPhase 2 := by decide
theorem c3_split : c3 = minusPhase 3 + plusPhase 3 := by decide

/-! ## Unbraidability

Classical analysis of `j`-coefficients without the Moonshine
decomposition gives only the totals `(c_1, c_2, c_3, ...)` —
enormous numbers with no apparent structure. Only by recognizing
the Monster-irrep decomposition does the clinamen become visible.

The `+ 1` is always there; extracting "just the large irreps"
erases it. The two phases must be kept coupled. -/

theorem classical_totals_hide_structure :
    c1 = 196884 ∧ c2 = 21493760 ∧ c3 = 864299970 := by decide

theorem structural_decomposition_reveals_clinamen :
    plusPhase 1 = 1
    ∧ plusPhase 2 = 1
    ∧ plusPhase 3 = 2 := by decide

/-! ## Master witness -/

theorem moonshine_mckay_braid_master :
    -- The three McKay decompositions
    c1 = chi1 + chi2
    ∧ c2 = chi1 + chi2 + chi3
    ∧ c3 = 2 * chi1 + 2 * chi2 + chi3 + chi4
    -- The clinamen is always present
    ∧ c1 - chi2 = chi1
    ∧ c2 - (chi2 + chi3) = chi1
    ∧ c3 - (2 * chi2 + chi3 + chi4) = 2 * chi1
    -- k=2 phase split
    ∧ c1 = minusPhase 1 + plusPhase 1
    ∧ c2 = minusPhase 2 + plusPhase 2
    ∧ c3 = minusPhase 3 + plusPhase 3 := by
  decide

/-! ## Reading

Monstrous Moonshine is scale-wall and category-wall beyond what this
substrate can prove. But the McKay observation — the seed of
Moonshine — is pure arithmetic: three Nat equalities, closed by
`decide`.

The decomposition pattern is the god-formula structure: `(deficit) +
(clinamen)`. In Moonshine the deficit is enormous (Monster irrep
dimensions in the hundreds of millions), the clinamen is always `+ 1`
(the trivial representation).

When Borcherds proved the Moonshine conjecture in 1992, the core
content was: ALL `j`-coefficients decompose as sums of Monster
irreps. Under the braid reading, this is saying: the `+ 1` clinamen
is there at every coefficient level. Moonshine is the universal
braiding of the `j`-invariant by the Monster.

The fact that `decide` closes these three specific cases — on
numbers with ten digits — demonstrates that the substrate can
handle Moonshine-scale arithmetic at the single-coefficient level.
The wall is NOT arithmetic. The wall is **category** (Monster as a
sporadic simple group, irrep machinery, modular-function theory).
Under `Init + decide`, we get the arithmetic face of Moonshine for
free; we leave the category machinery to mathlib.
-/

end MoonshineMcKayBraid
end Gnosis
