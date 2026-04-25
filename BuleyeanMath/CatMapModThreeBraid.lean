import Init

/-!
# Cat Map on (ℤ/3)² — the k=4 Braid

Fills the `k=4` slot in `BraidMasterCatalog`. The cat map `A` has
order 4 on `(ℤ/3)²` (proved in `ArnoldCatMapOrder5.lean`). Starting
from seed `(1, 0)`, the orbit cycles through four distinct points
before returning.

## The 4-point orbit

    step 0: (1, 0)
    step 1: (2, 1)
    step 2: (2, 0)
    step 3: (1, 2)
    step 4: (1, 0)    — return

All four pre-return points distinct. Return at exactly `4`.

## Why the k=4 slot is hard to fill

`{2, 3, 4, 5, 6, 7, 10, 12}` — of these, `k ∈ {2, 3, 5, 7, 10, 12}`
already have catalog entries from earlier digs. `k = 4` and `k = 6`
were gaps. The cat map mod 3 fills `k=4`; the tensor product `ℤ/2 ×
ℤ/3 = Aeon-ish-but-not` or `ℤ/2 × ℤ/2 × ℤ/3 = ?` might eventually
fill `k=6` directly.

`import Init` only. Zero `sorry`, zero new `axiom`.
-/

namespace BuleyeanMath
namespace CatMapModThreeBraid

def catMap3 (p : Nat × Nat) : Nat × Nat :=
  ((2 * p.1 + p.2) % 3, (p.1 + p.2) % 3)

def iterateCat3 : Nat → Nat × Nat → Nat × Nat
  | 0,     p => p
  | n + 1, p => iterateCat3 n (catMap3 p)

/-! ## The four-point orbit -/

theorem orbit_0 : iterateCat3 0 (1, 0) = (1, 0) := by decide
theorem orbit_1 : iterateCat3 1 (1, 0) = (2, 1) := by decide
theorem orbit_2 : iterateCat3 2 (1, 0) = (2, 0) := by decide
theorem orbit_3 : iterateCat3 3 (1, 0) = (1, 2) := by decide
theorem orbit_4 : iterateCat3 4 (1, 0) = (1, 0) := by decide

theorem no_return_at_1 : iterateCat3 1 (1, 0) ≠ (1, 0) := by decide
theorem no_return_at_2 : iterateCat3 2 (1, 0) ≠ (1, 0) := by decide
theorem no_return_at_3 : iterateCat3 3 (1, 0) ≠ (1, 0) := by decide

/-! ## Visit list -/

def visitList : List (Nat × Nat) :=
  [ (1, 0), (2, 1), (2, 0), (1, 2) ]

theorem visit_length : visitList.length = 4 := by decide

theorem visit_is_orbit :
    visitList = [ iterateCat3 0 (1, 0)
                , iterateCat3 1 (1, 0)
                , iterateCat3 2 (1, 0)
                , iterateCat3 3 (1, 0) ] := by decide

/-! ## Distinctness of the four points -/

theorem all_distinct :
    (1, 0) ≠ ((2, 1) : Nat × Nat)
    ∧ (1, 0) ≠ ((2, 0) : Nat × Nat)
    ∧ (1, 0) ≠ ((1, 2) : Nat × Nat)
    ∧ (2, 1) ≠ ((2, 0) : Nat × Nat)
    ∧ (2, 1) ≠ ((1, 2) : Nat × Nat)
    ∧ (2, 0) ≠ ((1, 2) : Nat × Nat) := by decide

/-! ## Master witness -/

theorem cat_map_mod_three_braid_master :
    iterateCat3 0 (1, 0) = (1, 0)
    ∧ iterateCat3 1 (1, 0) = (2, 1)
    ∧ iterateCat3 2 (1, 0) = (2, 0)
    ∧ iterateCat3 3 (1, 0) = (1, 2)
    ∧ iterateCat3 4 (1, 0) = (1, 0)
    ∧ iterateCat3 1 (1, 0) ≠ (1, 0)
    ∧ iterateCat3 2 (1, 0) ≠ (1, 0)
    ∧ iterateCat3 3 (1, 0) ≠ (1, 0)
    ∧ visitList.length = 4 := by
  decide

end CatMapModThreeBraid
end BuleyeanMath
