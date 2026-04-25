import Init

/-!
# Mesh Resonance: dot-product threshold filter on fixed-dimension state vectors

This module instantiates the **Resonance Invariant** named in
`FORMAL_LEDGER.md` (line 201): two peers `P_A` and `P_B` with state
vectors `V_A, V_B` "resonate" at threshold `τ` when
`V_A · V_B ≥ τ`.

We do not claim this construction produces an "unforgeable" connection
or any cryptographic property. The file formalizes the finite algebraic
filter — threshold on an integer dot product — and witnesses four
concrete facts that a downstream peer-matching layer would rely on:

* **Self-resonance.** Every vector `v` passes the resonance filter
  against itself at the threshold equal to its squared norm
  `‖v‖² = v · v`.
* **Symmetry.** `dotProduct v w = dotProduct w v` on every input.
* **Threshold monotonicity.** Lowering the threshold preserves
  resonance: `resonates v w τ₁ → τ₂ ≤ τ₁ → resonates v w τ₂`.
* **Anti-resonance witness.** A concrete pair `(v, w, τ)` where
  `dotProduct v w < τ`, showing the filter is not vacuously true.

State vectors are `Vector := List Int` of fixed dimension
`meshDim := 4`; the dot product iterates componentwise over the two
lists, returning `0` when lengths differ (this branch does not fire on
the canonical use of `Vector` at the fixed dimension).

## What is and is not proved

**Proved** (each below, closed by concrete `decide` or by structural
induction on `List Int`):

* `dotProduct_comm` in full generality on `List Int` by induction.
* `resonates_self` for every vector (the threshold is its squared norm).
* `resonates_mono` (threshold monotonicity).
* Concrete self-resonance, symmetry, and anti-resonance examples on
  four-dimensional integer vectors.

**Not proved.** We make no cryptographic or unforgeability claim. An
integer dot product exceeding a threshold is an algebraic filter, not
a proof of identity, authentication, or peer integrity; any such
property would require additional layers (signatures, commitments,
noise bounds) that are outside the scope of this module.

No `sorry`, no new `axiom`, `Init`-only.
-/

namespace Gnosis
namespace MeshResonance

/-! ## State vectors -/

/-- State vectors are integer lists. The canonical use fixes their
length at `meshDim`, but definitions below work for any length. -/
abbrev Vector := List Int

/-- The canonical mesh dimension used in concrete examples. -/
def meshDim : Nat := 4

/-! ## Dot product and squared norm -/

/-- Componentwise dot product on two integer lists. When the lists
have different lengths, missing positions contribute `0`, so the
function effectively truncates to the shorter length. -/
def dotProduct : Vector → Vector → Int
  | [],       _        => 0
  | _,        []       => 0
  | a :: as, b :: bs  => a * b + dotProduct as bs

/-- Squared norm `‖v‖² = v · v`, computed directly to avoid referring
to `dotProduct v v` in the self-resonance threshold. -/
def sumOfSquares : Vector → Int
  | []      => 0
  | a :: as => a * a + sumOfSquares as

/-! ## The resonance relation -/

/-- Peers `v, w` resonate at threshold `τ` when their dot product
meets or exceeds `τ`. -/
def resonates (v w : Vector) (τ : Int) : Prop := dotProduct v w ≥ τ

instance resonates_decidable (v w : Vector) (τ : Int) :
    Decidable (resonates v w τ) := by
  unfold resonates
  exact inferInstance

/-! ## General structural properties on `List Int` -/

/-- Commutativity of the dot product, by induction on both lists. -/
theorem dotProduct_comm : ∀ (v w : Vector), dotProduct v w = dotProduct w v
  | [],       []       => rfl
  | [],       _ :: _   => rfl
  | _ :: _,   []       => rfl
  | a :: as, b :: bs => by
      simp [dotProduct, dotProduct_comm as bs, Int.mul_comm]

/-- `sumOfSquares v` equals `dotProduct v v` for every vector. -/
theorem sumOfSquares_eq_dot : ∀ (v : Vector), sumOfSquares v = dotProduct v v
  | []      => rfl
  | a :: as => by
      simp [sumOfSquares, dotProduct, sumOfSquares_eq_dot as]

/-- **Self-resonance.** Every vector resonates with itself at the
threshold equal to its squared norm. -/
theorem resonates_self (v : Vector) : resonates v v (sumOfSquares v) := by
  unfold resonates
  rw [sumOfSquares_eq_dot]
  exact Int.le_refl _

/-- **Threshold monotonicity.** If `v` and `w` resonate at `τ₁` and
`τ₂ ≤ τ₁`, they also resonate at `τ₂`. -/
theorem resonates_mono {v w : Vector} {τ₁ τ₂ : Int}
    (h : resonates v w τ₁) (hτ : τ₂ ≤ τ₁) : resonates v w τ₂ := by
  unfold resonates at h ⊢
  exact Int.le_trans hτ h

/-! ## Concrete four-dimensional witnesses -/

/-- A specific mesh-dim vector. -/
def v1 : Vector := [1, 2, 3, 4]

/-- A second specific mesh-dim vector. -/
def v2 : Vector := [2, 0, 1, 5]

/-- A third specific mesh-dim vector, chosen so `v1 · v3 < 0`. -/
def v3 : Vector := [-3, -1, -1, -2]

/-- `v1 · v1 = 1 + 4 + 9 + 16 = 30`. -/
theorem dot_v1_v1 : dotProduct v1 v1 = 30 := by decide

/-- `v1 · v2 = 2 + 0 + 3 + 20 = 25`. -/
theorem dot_v1_v2 : dotProduct v1 v2 = 25 := by decide

/-- `v1 · v3 = -3 - 2 - 3 - 8 = -16`. -/
theorem dot_v1_v3 : dotProduct v1 v3 = -16 := by decide

/-- Concrete self-resonance at threshold `30`. -/
theorem resonates_v1_self : resonates v1 v1 30 := by decide

/-- Concrete cross-resonance at threshold `25`. -/
theorem resonates_v1_v2_25 : resonates v1 v2 25 := by decide

/-- Concrete cross-resonance holds at any lower threshold too. -/
theorem resonates_v1_v2_20 : resonates v1 v2 20 := by decide

/-- **Anti-resonance witness.** `v1` and `v3` do not resonate at the
threshold `0`; their dot product is `-16 < 0`. This demonstrates the
filter is not vacuously true. -/
theorem not_resonates_v1_v3_0 : ¬ resonates v1 v3 0 := by decide

/-- Strict anti-resonance: even at the very permissive threshold
`-10`, `v1` and `v3` still fail the filter because `-16 < -10`. -/
theorem not_resonates_v1_v3_neg10 : ¬ resonates v1 v3 (-10) := by decide

/-- Symmetry instance: `v1 · v2 = v2 · v1`. -/
theorem symmetry_v1_v2 : dotProduct v1 v2 = dotProduct v2 v1 := by decide

/-- Symmetry instance: `v1 · v3 = v3 · v1`. -/
theorem symmetry_v1_v3 : dotProduct v1 v3 = dotProduct v3 v1 := by decide

/-! ## Monotonicity on concrete thresholds -/

/-- Lowering a passing threshold preserves resonance: if `v1, v2`
resonate at `25`, they resonate at `10`. -/
theorem resonates_mono_v1_v2 :
    resonates v1 v2 10 := by
  exact resonates_mono resonates_v1_v2_25 (by decide)

/-! ## Aggregate witness

One decidable bundle that pins down the three core resonance facts on
`(v1, v2, v3)`: positive self-resonance, positive cross-resonance, and
a concrete anti-resonance failure. -/

/-- Aggregate mesh-resonance witness. The threshold filter is
positive on aligned vectors and negative on anti-aligned ones. -/
theorem mesh_resonance_instances :
    dotProduct v1 v1 = 30 ∧
    dotProduct v1 v2 = 25 ∧
    dotProduct v1 v3 = -16 ∧
    (decide (resonates v1 v1 30)) = true ∧
    (decide (resonates v1 v2 25)) = true ∧
    (decide (resonates v1 v3 0)) = false := by
  decide

end MeshResonance
end Gnosis
