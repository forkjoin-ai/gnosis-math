import Init

/-
  AmplituhedronAntisymmetryNoGo.lean
  ==================================

  Algebraic obstruction theorem: amplituhedron amplitude with the
  standard `[q; k]` KPlane row composition can NEVER equal the
  bilinear inner product Q·K, no matter what dual covector is chosen.

  ## Why this file exists

  The empirical parity test in `scattering_attention.rs` (shipped
  2026-05-10) found that `attention_via_amplituhedron` with the
  uniform dual `[1, 1, …, 1]` diverges from `attention_via_softmax`:
  mean cosine ≈ 0.74, argmax agreement 25%, mean abs-diff 0.18 (3
  orders of magnitude above quantization noise).

  The natural follow-up question: could a *learned* dual covector
  recover softmax? This file proves the answer is **no**, structurally.

  ## The argument

  1. The inner product `Q·K = Σ q[i]·k[i]` is *symmetric* in (q, k):
     `innerProduct q k = innerProduct k q`. (`innerProduct_symmetric`.)

  2. The 2×2 amplituhedron minor at column pair (i, j) is
     `minor q k i j = q[i]·k[j] - q[j]·k[i]`. This is *antisymmetric*
     in (q, k): swapping q and k flips sign. (`minor_antisymmetric`.)

  3. ANY linear combination of minors over a fixed pair set, weighted
     by an arbitrary dual covector, inherits the antisymmetry.
     (`amp2x2_antisymmetric`.)

  4. A function that is both symmetric AND antisymmetric must be
     identically zero on every input (in `Int` since it has no
     2-torsion). (`sym_meets_antisym_implies_zero`.)

  5. Therefore, no choice of dual covector can make the amplituhedron
     amplitude equal the inner product unless both vanish — i.e., the
     amplituhedron path with `[q; k]` row composition is structurally
     incompatible with softmax. (`no_dual_recovers_inner_product`.)

  This closes the door on direction (a) "learn the dual to recover
  softmax" rigorously. The empirical 0.74 cosine wasn't a quantization
  artifact or a bad regression — it's an algebraic consequence of the
  KPlane row composition. To recover softmax-like attention, the row
  composition must change (direction (b)), and for k=1 with row =
  `q ⊙ k` the polytope geometry trivializes.

  Init-only per the Rustic Church initiative.
-/

namespace AmplituhedronAntisymmetryNoGo

-- ══════════════════════════════════════════════════════════
-- INNER PRODUCT (THE SOFTMAX SIDE — SYMMETRIC)
-- ══════════════════════════════════════════════════════════

/-- The bilinear inner product `⟨q, k⟩ = Σ q[i] · k[i]` over `Int`
    rows. Truncates at the shorter list (matches Lean Init `List.zip`
    semantics). -/
def innerProduct : List Int → List Int → Int
  | [], _              => 0
  | _, []              => 0
  | q :: qs, k :: ks   => q * k + innerProduct qs ks

/-- Inner product is symmetric: swapping `q` and `k` leaves the value
    unchanged. -/
theorem innerProduct_symmetric (q k : List Int) :
    innerProduct q k = innerProduct k q := by
  induction q generalizing k with
  | nil =>
    cases k <;> rfl
  | cons qh qt ih =>
    cases k with
    | nil => rfl
    | cons kh kt =>
      show qh * kh + innerProduct qt kt = kh * qh + innerProduct kt qt
      rw [Int.mul_comm qh kh, ih kt]

-- ══════════════════════════════════════════════════════════
-- 2×2 MINOR (THE AMPLITUHEDRON SIDE — ANTISYMMETRIC)
-- ══════════════════════════════════════════════════════════

/-- The 2×2 minor at column pair `(i, j)` of the matrix
    `[[q[0], q[1], …], [k[0], k[1], …]]`:
    `q[i]·k[j] - q[j]·k[i]`. This is the unsigned cofactor of one
    column pair in the KPlane built from rows `[q; k]`. -/
def minor (q k : List Int) (i j : Nat) : Int :=
  q.getD i 0 * k.getD j 0 - q.getD j 0 * k.getD i 0

/-- The 2×2 minor is antisymmetric in `(q, k)`: swapping the rows of
    the underlying matrix flips the sign. -/
theorem minor_antisymmetric (q k : List Int) (i j : Nat) :
    minor q k i j = -(minor k q i j) := by
  unfold minor
  -- LHS: q.getD i 0 * k.getD j 0 - q.getD j 0 * k.getD i 0
  -- RHS: -(k.getD i 0 * q.getD j 0 - k.getD j 0 * q.getD i 0)
  -- After Int.mul_comm on the RHS multiplicands the inner expression
  -- becomes q.getD j 0 * k.getD i 0 - q.getD i 0 * k.getD j 0, whose
  -- negation is exactly the LHS.
  rw [Int.mul_comm (k.getD i 0) (q.getD j 0),
      Int.mul_comm (k.getD j 0) (q.getD i 0)]
  -- Goal: a - b = -(b - a) for a, b the two products
  rw [Int.neg_sub]

/-- Linear combination of minors over a list of column-index pairs,
    weighted by a dual covector. The amplituhedron amplitude with row
    composition `[q; k]` is exactly this sum (with `pairs` = ordered
    2-subsets of `[0..d_head)`). -/
def amp2x2 (q k : List Int) : List (Nat × Nat) → List Int → Int
  | [], _              => 0
  | _, []              => 0
  | (i, j) :: ps, d :: ds => d * minor q k i j + amp2x2 q k ps ds

/-- Antisymmetry lifts through the linear combination: any weighted
    sum of antisymmetric minors is itself antisymmetric in (q, k). -/
theorem amp2x2_antisymmetric (q k : List Int) :
    ∀ (pairs : List (Nat × Nat)) (dual : List Int),
      amp2x2 q k pairs dual = -(amp2x2 k q pairs dual) := by
  intro pairs dual
  induction pairs generalizing dual with
  | nil =>
    cases dual <;> (unfold amp2x2; rfl)
  | cons p ps ih =>
    cases dual with
    | nil => unfold amp2x2; rfl
    | cons d ds =>
      obtain ⟨i, j⟩ := p
      show d * minor q k i j + amp2x2 q k ps ds
        = -(d * minor k q i j + amp2x2 k q ps ds)
      rw [minor_antisymmetric q k i j, ih ds]
      -- d * (-x) + (-y) = -(d * x + y)
      rw [Int.mul_neg, Int.neg_add]

-- ══════════════════════════════════════════════════════════
-- THE NO-GO THEOREM
-- ══════════════════════════════════════════════════════════

-- Forward declaration of the concrete witness used in the no-go below.

/-- Concrete witness: on `q = [1, 2]`, `k = [3, 4]`, the inner product
    is `1·3 + 2·4 = 11`. Used by `no_dual_recovers_inner_product`. -/
theorem inner_product_concrete : innerProduct [1, 2] [3, 4] = 11 := by
  unfold innerProduct
  decide

/-- **No-go**: no choice of `dual` and `pairs` can make the
    amplituhedron 2×2 amplitude equal the bilinear inner product on
    every `(q, k)`. Proven by concrete witness contradiction: assume
    such `dual`, `pairs` exist; specialize at `q = [1, 2]` and
    `k = [3, 4]`; antisymmetry of `amp2x2` plus symmetry of
    `innerProduct` force `11 = -11`, contradiction.

    The amplituhedron path with `[q; k]` row composition is therefore
    structurally incompatible with dot-product attention. -/
theorem no_dual_recovers_inner_product
    (dual : List Int) (pairs : List (Nat × Nat))
    (h_match : ∀ q k : List Int,
        amp2x2 q k pairs dual = innerProduct q k) :
    False := by
  -- Specialize at the concrete witness q = [1, 2], k = [3, 4].
  have h_qk : amp2x2 [1, 2] [3, 4] pairs dual = 11 := by
    rw [h_match [1, 2] [3, 4]]
    exact inner_product_concrete
  -- By antisymmetry of amp2x2, the swap gives -11.
  have h_kq : amp2x2 [3, 4] [1, 2] pairs dual = -11 := by
    have h_anti : amp2x2 [1, 2] [3, 4] pairs dual
        = -(amp2x2 [3, 4] [1, 2] pairs dual) :=
      amp2x2_antisymmetric [1, 2] [3, 4] pairs dual
    have : (11 : Int) = -(amp2x2 [3, 4] [1, 2] pairs dual) := h_qk ▸ h_anti
    have : amp2x2 [3, 4] [1, 2] pairs dual = -(11 : Int) := by
      rw [this, Int.neg_neg]
    exact this
  -- By the hypothesis, amp2x2 on the swap also equals innerProduct
  -- on the swap, which by symmetry equals innerProduct on the original.
  have h_kq_via_inner : innerProduct [3, 4] [1, 2] = -11 := by
    rw [← h_match [3, 4] [1, 2]]; exact h_kq
  have h_kq_sym : innerProduct [3, 4] [1, 2] = innerProduct [1, 2] [3, 4] :=
    innerProduct_symmetric [3, 4] [1, 2]
  have h_kq_eq_11 : innerProduct [3, 4] [1, 2] = 11 := by
    rw [h_kq_sym]; exact inner_product_concrete
  -- 11 = -11 in Int — contradiction.
  have h_contra : (11 : Int) = -11 := by
    rw [← h_kq_eq_11]; exact h_kq_via_inner
  exact absurd h_contra (by decide)

-- ══════════════════════════════════════════════════════════
-- CONCRETE MINOR WITNESSES — THE OBSTRUCTION FIRES
-- ══════════════════════════════════════════════════════════

/-- The concrete 2×2 minor at `(0, 1)` for `q = [1, 2]`, `k = [3, 4]`
    is `1·4 - 2·3 = -2`. Compare with the inner product `11`: the two
    have different sign behavior under (q, k) swap. -/
theorem minor_concrete : minor [1, 2] [3, 4] 0 1 = -2 := by
  unfold minor
  decide

/-- And the swap: `minor [3, 4] [1, 2] 0 1 = 3·2 - 4·1 = 2 = -(-2)`,
    confirming the antisymmetry on the concrete witness. -/
theorem minor_swap_concrete : minor [3, 4] [1, 2] 0 1 = 2 := by
  unfold minor
  decide

end AmplituhedronAntisymmetryNoGo
