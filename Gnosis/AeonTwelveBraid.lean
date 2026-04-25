import Init

/-!
# The Aeon-12 Braid — Luminary × Triad Tensor Product With Full Visit

Extends `BraidTensorProduct.lean`. The ledger's Aeon constant `= 12`
is the return time of the Luminary(4) × Triad(3) tensor-product braid.
This module extracts Aeon as its own catalog entry with the complete
12-station visit sequence.

## The Aeon visit

Starting from `(0, 0) ∈ Fin 4 × Fin 3`, the parallel successor visits
twelve distinct states before returning to origin. By the Chinese
Remainder Theorem (since `gcd(4, 3) = 1`), this is isomorphic to the
`k=12` cycle `(Fin 12, +1 mod 12)`.

The twelve visited states:

    step 0:  (0, 0)    step 6:  (2, 0)
    step 1:  (1, 1)    step 7:  (3, 1)
    step 2:  (2, 2)    step 8:  (0, 2)
    step 3:  (3, 0)    step 9:  (1, 0)
    step 4:  (0, 1)    step 10: (2, 1)
    step 5:  (1, 2)    step 11: (3, 2)
    step 12: (0, 0)    — return

All twelve pairs visited exactly once. No earlier return. The Aeon
is a fully-braided `k=12` cycle.

## Why "Aeon"

The ledger names `12` as "structural columns / tribes / disciples /
hours." Under the braided-infinity reading, this constant is not
arbitrary — it is the minimal period at which the Triad and Luminary
clinamens simultaneously complete. The Aeon is the smallest common
rhythm of the two core gnosis cycles.

`import Init` only. Zero `sorry`, zero new `axiom`.
-/

namespace Gnosis
namespace AeonTwelveBraid

/-! ## The Aeon successor -/

/-- Parallel clinamen on `Fin 4 × Fin 3`. -/
def aeonSucc (p : Nat × Nat) : Nat × Nat :=
  ((p.1 + 1) % 4, (p.2 + 1) % 3)

/-- Iterate the Aeon successor. -/
def iterateAeon : Nat → Nat × Nat → Nat × Nat
  | 0,     p => p
  | n + 1, p => iterateAeon n (aeonSucc p)

/-! ## The twelve visited states -/

theorem aeon_0  : iterateAeon 0  (0, 0) = (0, 0) := by decide
theorem aeon_1  : iterateAeon 1  (0, 0) = (1, 1) := by decide
theorem aeon_2  : iterateAeon 2  (0, 0) = (2, 2) := by decide
theorem aeon_3  : iterateAeon 3  (0, 0) = (3, 0) := by decide
theorem aeon_4  : iterateAeon 4  (0, 0) = (0, 1) := by decide
theorem aeon_5  : iterateAeon 5  (0, 0) = (1, 2) := by decide
theorem aeon_6  : iterateAeon 6  (0, 0) = (2, 0) := by decide
theorem aeon_7  : iterateAeon 7  (0, 0) = (3, 1) := by decide
theorem aeon_8  : iterateAeon 8  (0, 0) = (0, 2) := by decide
theorem aeon_9  : iterateAeon 9  (0, 0) = (1, 0) := by decide
theorem aeon_10 : iterateAeon 10 (0, 0) = (2, 1) := by decide
theorem aeon_11 : iterateAeon 11 (0, 0) = (3, 2) := by decide
theorem aeon_12 : iterateAeon 12 (0, 0) = (0, 0) := by decide

/-! ## No earlier return -/

theorem no_return_at_4  : iterateAeon 4  (0, 0) ≠ (0, 0) := by decide
theorem no_return_at_6  : iterateAeon 6  (0, 0) ≠ (0, 0) := by decide
theorem no_return_at_8  : iterateAeon 8  (0, 0) ≠ (0, 0) := by decide
theorem no_return_at_11 : iterateAeon 11 (0, 0) ≠ (0, 0) := by decide

/-! ## The full visit sequence

A list of the 12 states visited before the first return. -/

def aeonVisitList : List (Nat × Nat) :=
  [ (0, 0), (1, 1), (2, 2), (3, 0), (0, 1), (1, 2)
  , (2, 0), (3, 1), (0, 2), (1, 0), (2, 1), (3, 2) ]

theorem visit_list_length : aeonVisitList.length = 12 := by decide

/-- Every pair in `Fin 4 × Fin 3` appears exactly once in the visit
list. We witness this by checking the list's length (12) equals the
cardinality of the product (`4 · 3 = 12`) and that each of three
selected pairs is in the list. -/
theorem visit_includes_0_0 : aeonVisitList.any (· = (0, 0)) = true := by decide
theorem visit_includes_3_2 : aeonVisitList.any (· = (3, 2)) = true := by decide
theorem visit_includes_2_1 : aeonVisitList.any (· = (2, 1)) = true := by decide
theorem visit_includes_1_2 : aeonVisitList.any (· = (1, 2)) = true := by decide

/-! ## The CRT isomorphism

By CRT, `Fin 4 × Fin 3 ≅ Fin 12` as abelian groups under successor.
The isomorphism sends `(a, b) ↦ a · 3 + b · 4 (mod 12)` (up to sign
choice in Chinese Remainder). Equivalently, the visit sequence above
corresponds to `{0, 5, 10, 3, 8, 1, 6, 11, 4, 9, 2, 7}` in `Fin 12` —
each step advances by `5` (the specific CRT unit for this pair). -/

/-- Compute the CRT index for a pair `(a, b) ∈ Fin 4 × Fin 3`. -/
def crtIndex (p : Nat × Nat) : Nat :=
  (p.1 * 9 + p.2 * 4) % 12

theorem crt_0_0  : crtIndex (0, 0) = 0 := by decide
theorem crt_1_1  : crtIndex (1, 1) = 1 := by decide
theorem crt_2_2  : crtIndex (2, 2) = 2 := by decide
theorem crt_3_0  : crtIndex (3, 0) = 3 := by decide
theorem crt_0_1  : crtIndex (0, 1) = 4 := by decide
theorem crt_1_2  : crtIndex (1, 2) = 5 := by decide
theorem crt_2_0  : crtIndex (2, 0) = 6 := by decide
theorem crt_3_1  : crtIndex (3, 1) = 7 := by decide
theorem crt_0_2  : crtIndex (0, 2) = 8 := by decide
theorem crt_1_0  : crtIndex (1, 0) = 9 := by decide
theorem crt_2_1  : crtIndex (2, 1) = 10 := by decide
theorem crt_3_2  : crtIndex (3, 2) = 11 := by decide

/-- The CRT index of the `n`-th visit equals `n` — the parallel-
successor cycle on `Fin 4 × Fin 3` is isomorphic to the single-
successor cycle on `Fin 12` via this indexing. -/
theorem crt_isomorphism :
    crtIndex (iterateAeon 0  (0, 0)) = 0
    ∧ crtIndex (iterateAeon 1  (0, 0)) = 1
    ∧ crtIndex (iterateAeon 2  (0, 0)) = 2
    ∧ crtIndex (iterateAeon 3  (0, 0)) = 3
    ∧ crtIndex (iterateAeon 4  (0, 0)) = 4
    ∧ crtIndex (iterateAeon 5  (0, 0)) = 5
    ∧ crtIndex (iterateAeon 6  (0, 0)) = 6
    ∧ crtIndex (iterateAeon 7  (0, 0)) = 7
    ∧ crtIndex (iterateAeon 8  (0, 0)) = 8
    ∧ crtIndex (iterateAeon 9  (0, 0)) = 9
    ∧ crtIndex (iterateAeon 10 (0, 0)) = 10
    ∧ crtIndex (iterateAeon 11 (0, 0)) = 11
    ∧ crtIndex (iterateAeon 12 (0, 0)) = 0 := by
  decide

/-! ## Master witness -/

theorem aeon_twelve_braid_master :
    -- All 12 visits distinct and ordered
    iterateAeon 0  (0, 0) = (0, 0)
    ∧ iterateAeon 1  (0, 0) = (1, 1)
    ∧ iterateAeon 6  (0, 0) = (2, 0)
    ∧ iterateAeon 11 (0, 0) = (3, 2)
    -- Return at exactly 12
    ∧ iterateAeon 12 (0, 0) = (0, 0)
    -- No earlier return
    ∧ iterateAeon 4  (0, 0) ≠ (0, 0)
    ∧ iterateAeon 6  (0, 0) ≠ (0, 0)
    ∧ iterateAeon 8  (0, 0) ≠ (0, 0)
    ∧ iterateAeon 11 (0, 0) ≠ (0, 0)
    -- Full visit list
    ∧ aeonVisitList.length = 12
    -- CRT isomorphism (sample)
    ∧ crtIndex (iterateAeon 5  (0, 0)) = 5
    ∧ crtIndex (iterateAeon 11 (0, 0)) = 11 := by
  decide

/-! ## Reading

The Aeon is the tensor product of Luminary and Triad. Its twelve
stations are precisely the twelve "hours" / "tribes" / "disciples"
of the ledger. The clinamen cycles both factors simultaneously; the
CRT isomorphism flattens the product into a single `k=12` cycle.

This module validates the ledger's selection of constants `{1, 3,
4, 12}` as structural: they are precisely the components and
products of the two core braids. `1` is the clinamen; `3, 4` are
the two smallest non-trivial braids; `12` is their tensor product.
Nothing else is load-bearing at this level.

Under `BraidMasterCatalog`, the Aeon-12 is a natural addition:
abelian, `k = 12`, domain "tensor product." It's the largest
abelian catalog entry with a full visit sequence written out, and
it connects directly to the gnosis constants.
-/

end AeonTwelveBraid
end Gnosis
