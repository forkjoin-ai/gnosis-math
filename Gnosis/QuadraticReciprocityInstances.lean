import Init

/-!
# Quadratic Reciprocity on Small Odd Prime Instances

This module computes the Legendre symbol `(a / p)` for an odd prime `p`
by brute enumeration of the nonzero quadratic residues mod `p`, and
witnesses several concrete cases of Gauss's quadratic reciprocity law
and its first supplement.

The Legendre symbol here evaluates as

    (a / p) = 0                      if p ∣ a
             = 1                      if (a mod p) is a nonzero square mod p
             = -1                     otherwise.

The nonzero squares mod `p` are produced by squaring each of
`1, 2, ..., (p-1)/2` and reducing mod `p`; this exhausts the image of
the squaring map on `(ℤ/p)^×` because the map is 2-to-1 and its image
has size `(p-1)/2`.

Quadratic reciprocity states

    (q / p) · (p / q) = (-1)^(((p-1)/2) · ((q-1)/2))

for distinct odd primes `p, q`. The first supplement states

    (-1 / p) = (-1)^((p-1)/2).

We close each small instance by `decide` after the `legendre`
computation reduces to a small integer. The general theorem
(Gauss's law across all odd prime pairs) is not proved here; what is
witnessed is a finite list of numerical coincidences that the general
theorem implies.

No `sorry`, no new `axiom`, `Init`-only.
-/

namespace Gnosis
namespace QuadraticReciprocityInstances

/-! ## Quadratic residues enumerated via squaring -/

/-- Nonzero quadratic residues mod `p` listed by squaring
`1, 2, ..., (p-1)/2` and reducing. Works for any `p ≥ 2`; for odd
prime `p` every nonzero square occurs exactly once in this list. -/
def quadraticResidues (p : Nat) : List Nat :=
  let half := (p - 1) / 2
  (List.range half).map (fun k => ((k + 1) * (k + 1)) % p)

/-- Decidable membership check for `n ∈ xs` on `List Nat`. -/
def memNat (n : Nat) : List Nat → Bool
  | [] => false
  | x :: xs => if x = n then true else memNat n xs

/-- Legendre symbol `(a / p)` as an `Int`. Returns `0` when `p ∣ a`,
`1` when `a mod p` is a nonzero square mod `p`, and `-1` otherwise. -/
def legendre (a p : Nat) : Int :=
  let r := a % p
  if r = 0 then 0
  else if memNat r (quadraticResidues p) then 1
  else -1

/-! ## Sanity checks for the Legendre computation -/

/-- Divisibility case: `(6 / 3) = 0` because `3 ∣ 6`. -/
theorem legendre_div_zero : legendre 6 3 = 0 := by decide

/-- The quadratic residues mod 5 are `{1, 4}`. -/
theorem residues_mod_5 : quadraticResidues 5 = [1, 4] := by decide

/-- The quadratic residues mod 7 are `{1, 4, 2}`. -/
theorem residues_mod_7 : quadraticResidues 7 = [1, 4, 2] := by decide

/-- `(2 / 5) = -1`: `2` is a nonresidue mod 5. -/
theorem legendre_2_5 : legendre 2 5 = -1 := by decide

/-- `(4 / 5) = 1`: `4 = 2²` is a residue mod 5. -/
theorem legendre_4_5 : legendre 4 5 = 1 := by decide

/-! ## Right-hand side sign `(-1)^(((p-1)/2)·((q-1)/2))` -/

/-- Integer power with `Int` base and `Nat` exponent. -/
def intPow (x : Int) : Nat → Int
  | 0 => 1
  | Nat.succ k => x * intPow x k

/-- Right-hand side of quadratic reciprocity for odd primes `p, q`. -/
def reciprocityRHS (p q : Nat) : Int :=
  intPow (-1) (((p - 1) / 2) * ((q - 1) / 2))

/-- Right-hand side of the first supplement for odd prime `p`. -/
def firstSupplementRHS (p : Nat) : Int :=
  intPow (-1) ((p - 1) / 2)

/-! ## Reciprocity instances

For each pair `(p, q)` below, both sides evaluate to concrete integers
and `decide` closes the equality. We do not appeal to a general proof
of Gauss's theorem; these are numerical witnesses.
-/

/-- Reciprocity for `(p, q) = (3, 5)`. Exponent `1·2 = 2`, RHS `= 1`. -/
theorem reciprocity_3_5 :
    legendre 5 3 * legendre 3 5 = reciprocityRHS 3 5 := by decide

/-- Reciprocity for `(p, q) = (3, 7)`. Exponent `1·3 = 3`, RHS `= -1`. -/
theorem reciprocity_3_7 :
    legendre 7 3 * legendre 3 7 = reciprocityRHS 3 7 := by decide

/-- Reciprocity for `(p, q) = (5, 7)`. Exponent `2·3 = 6`, RHS `= 1`. -/
theorem reciprocity_5_7 :
    legendre 7 5 * legendre 5 7 = reciprocityRHS 5 7 := by decide

/-- Reciprocity for `(p, q) = (7, 11)`. Exponent `3·5 = 15`, RHS `= -1`. -/
theorem reciprocity_7_11 :
    legendre 11 7 * legendre 7 11 = reciprocityRHS 7 11 := by decide

/-- Reciprocity for `(p, q) = (5, 13)`. Exponent `2·6 = 12`, RHS `= 1`. -/
theorem reciprocity_5_13 :
    legendre 13 5 * legendre 5 13 = reciprocityRHS 5 13 := by decide

/-! ## First supplement instances: `(-1 / p) = (-1)^((p-1)/2)`

We encode `-1 mod p` as `p - 1` so that `legendre` receives a `Nat`. -/

/-- First supplement at `p = 5`. Exponent `2`, RHS `= 1`; and
`4 = 2²` is a square mod 5 so LHS `= 1`. -/
theorem first_supplement_5 :
    legendre 4 5 = firstSupplementRHS 5 := by decide

/-- First supplement at `p = 7`. Exponent `3`, RHS `= -1`; and
`6` is a nonsquare mod 7 so LHS `= -1`. -/
theorem first_supplement_7 :
    legendre 6 7 = firstSupplementRHS 7 := by decide

/-- First supplement at `p = 13`. Exponent `6`, RHS `= 1`; and
`12` is a square mod 13 (since `5² = 25 ≡ 12`) so LHS `= 1`. -/
theorem first_supplement_13 :
    legendre 12 13 = firstSupplementRHS 13 := by decide

end QuadraticReciprocityInstances
end Gnosis
