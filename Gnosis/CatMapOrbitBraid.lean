import Init

/-!
# Arnold Cat Map Orbit as a k=10 Braid

Formalizes the cat map `A = [[2,1],[1,1]]` acting on `(ℤ/5)²` as a
`k=10` abelian braid. From `ArnoldCatMapOrder5.lean` we already have
`ord(A, 5) = 10`. Here we compile the full 10-point orbit as a
braided infinity with explicit visit sequence.

## The braid

The cat map has order 10 on `(ℤ/5)²`. Starting from seed `(1, 0)`,
the orbit cycles through exactly 10 distinct points before returning.
The clinamen is one application of `A`; ten applications return to
the seed. Standard abelian braid, `k = 10`.

## Unbraidability

Restricting to the subsequence `A^{10k}` (multiples of the period)
stays at `(1, 0)` forever. The 9 other orbit points are erased. For
non-trivial structure (the map's chaotic mixing on the torus), the
full 10-visit sequence is required.

`import Init` only. Zero `sorry`, zero new `axiom`.
-/

namespace Gnosis
namespace CatMapOrbitBraid

/-! ## The cat map mod 5 -/

/-- `A(x, y) = (2x + y, x + y)` mod 5. -/
def catMap (p : Nat × Nat) : Nat × Nat :=
  ((2 * p.1 + p.2) % 5, (p.1 + p.2) % 5)

/-- Iterate the cat map. -/
def iterateCat : Nat → Nat × Nat → Nat × Nat
  | 0,     p => p
  | n + 1, p => iterateCat n (catMap p)

/-! ## The 10-point orbit from seed `(1, 0)` -/

/- By iterating, the orbit is:
   (1,0), (2,1), (0,3), (3,3), (4,1), (4,0), (3,4), (0,2), (2,2),
   (1,4), (1,0)

   Ten distinct pre-return points; returns to (1,0) at step 10. -/

theorem orbit_step_0 : iterateCat 0 (1, 0) = (1, 0) := by decide
theorem orbit_step_1 : iterateCat 1 (1, 0) = (2, 1) := by decide
theorem orbit_step_2 : iterateCat 2 (1, 0) = (0, 3) := by decide
theorem orbit_step_3 : iterateCat 3 (1, 0) = (3, 3) := by decide
theorem orbit_step_4 : iterateCat 4 (1, 0) = (4, 1) := by decide
theorem orbit_step_5 : iterateCat 5 (1, 0) = (4, 0) := by decide
theorem orbit_step_6 : iterateCat 6 (1, 0) = (3, 4) := by decide
theorem orbit_step_7 : iterateCat 7 (1, 0) = (0, 2) := by decide
theorem orbit_step_8 : iterateCat 8 (1, 0) = (2, 2) := by decide
theorem orbit_step_9 : iterateCat 9 (1, 0) = (1, 4) := by decide
theorem orbit_step_10 : iterateCat 10 (1, 0) = (1, 0) := by decide

/-! ## The braid has period exactly 10

No earlier return. -/

theorem no_return_at_1 : iterateCat 1 (1, 0) ≠ (1, 0) := by decide
theorem no_return_at_2 : iterateCat 2 (1, 0) ≠ (1, 0) := by decide
theorem no_return_at_5 : iterateCat 5 (1, 0) ≠ (1, 0) := by decide
theorem no_return_at_9 : iterateCat 9 (1, 0) ≠ (1, 0) := by decide

/-! ## The visit sequence -/

def visitList : Nat → List (Nat × Nat)
  | 0     => []
  | n + 1 => visitList n ++ [iterateCat n (1, 0)]

theorem visit_10_covers_all :
    visitList 10 = [
      (1, 0), (2, 1), (0, 3), (3, 3), (4, 1),
      (4, 0), (3, 4), (0, 2), (2, 2), (1, 4)
    ] := by decide

/-! ## Unbraidability — subsequence extraction stays at the seed -/

/-- Subsequence at multiples of 10 stays put: `A^{10k}(v) = v`. -/
theorem restricted_at_10 : iterateCat 10 (1, 0) = (1, 0) := by decide
theorem restricted_at_20 : iterateCat 20 (1, 0) = (1, 0) := by decide
theorem restricted_at_30 : iterateCat 30 (1, 0) = (1, 0) := by decide

/-! ## Master witness -/

theorem cat_map_orbit_braid_master :
    -- Ten-step return
    iterateCat 10 (1, 0) = (1, 0)
    -- No earlier return
    ∧ iterateCat 1 (1, 0) ≠ (1, 0)
    ∧ iterateCat 2 (1, 0) ≠ (1, 0)
    ∧ iterateCat 5 (1, 0) ≠ (1, 0)
    ∧ iterateCat 9 (1, 0) ≠ (1, 0)
    -- Full visit covers 10 distinct points
    ∧ visitList 10 = [
        (1, 0), (2, 1), (0, 3), (3, 3), (4, 1),
        (4, 0), (3, 4), (0, 2), (2, 2), (1, 4)
      ]
    -- Restricted iteration stays at seed
    ∧ iterateCat 20 (1, 0) = (1, 0)
    ∧ iterateCat 30 (1, 0) = (1, 0) := by
  decide

/-! ## The k=10 braid slot

The cat map on `(ℤ/5)²` occupies the `k = 10` slot in the catalog —
the largest abelian braid formalized so far. Its ten phases are
concrete `Nat × Nat` pairs; the clinamen is a specific linear map,
not just `+1`; yet the braid structure is identical. A directed
`k`-cycle with uniform successor.

This demonstrates that the braid abstraction captures arbitrary
finite-order linear dynamics, not just modular arithmetic. Any
`SL(2, ℤ/n)` element `A` with finite order `m` generates a `k = m`
braid on its orbit. The successor operator is the specific action;
the braid structure is universal.

Under `TootsiePopBraidMixing.catMapMix`, this is the `k=10` entry
with `diameter = 9` and `returnSteps = 10`. Asymmetry of approach:
we touch nine orbit points before the tenth closes the cycle.
-/

end CatMapOrbitBraid
end Gnosis
