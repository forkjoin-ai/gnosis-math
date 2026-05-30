/-
  HurwitzDivisionAlgebras
  ========================

  The Hurwitz ladder of the four real normed division algebras and their
  Cayley–Dickson doubling:

      ℝ (dim 1) → ℂ (dim 2) → ℍ (dim 4) → 𝕆 (dim 8).

  Their dimensions are `[1, 2, 4, 8] = [2^0, 2^1, 2^2, 2^3]`, each obtained from
  the previous by **Cayley–Dickson doubling** (`dimₙ₊₁ = 2·dimₙ`). The four
  dimensions sum to `1 + 2 + 4 + 8 = 15 = 2^4 − 1`.

  HURWITZ'S THEOREM (CITED, not formalized here): up to isomorphism, ℝ, ℂ, ℍ, 𝕆
  are the *only* finite-dimensional normed division algebras over ℝ (equivalently,
  the only composition algebras with positive-definite norm). Adolf Hurwitz, 1898;
  the "1, 2, 4, 8 theorem". We formalize only the dimension/doubling arithmetic of
  the ladder, NOT a proof of the classification — that requires the full
  composition-algebra theory and is stated as a cited fact below.

  STRUCTURE LOST ON DOUBLING (CITED doc only):
    * ℝ → ℂ : loses the total **order** (ℝ is ordered; ℂ is not).
    * ℂ → ℍ : loses **commutativity** (ℍ is noncommutative).
    * ℍ → 𝕆 : loses **associativity** (𝕆 is nonassociative).
      𝕆 retains **alternativity** — the Moufang property formalized in
      `OctavianMoufangCubic` — which is the weakest associativity the
      classification still permits; the next doubling (sedenions, dim 16) loses
      even that and is no longer a division algebra.

  TIE-IN: `divAlgDims = FreudenthalMagicSquare.divDims = [1,2,4,8]` indexes the
  rows/cols of the Freudenthal–Tits magic square. The largest, `8 = dim 𝕆`,
  indexes the octonion row whose top entry is `E₈` of dimension `248`
  (`OctavianCubicMagicSquare.octonionDim = 8`, `dim E₈ = 248`).

  Init only. Kernel `decide`/`rfl`. Zero `sorry`, zero new `axiom`,
  no `Classical`, no `native_decide`.
-/

import Gnosis.FreudenthalMagicSquare
import Gnosis.OctavianCubicMagicSquare

namespace Gnosis.HurwitzDivisionAlgebras

-- ══════════════════════════════════════════════════════════
-- THE FOUR NORMED DIVISION-ALGEBRA DIMENSIONS
-- ══════════════════════════════════════════════════════════

/-- The dimensions of the four real normed division algebras ℝ, ℂ, ℍ, 𝕆. -/
def divAlgDims : List Nat := [1, 2, 4, 8]

/-- Symbolic names of the four algebras, in ladder order. -/
inductive HurwitzAlgebra
  | reals        -- ℝ
  | complexes    -- ℂ
  | quaternions  -- ℍ
  | octonions    -- 𝕆
deriving DecidableEq, Repr

/-- Dimension of each Hurwitz algebra. -/
def dim : HurwitzAlgebra → Nat
  | .reals       => 1
  | .complexes   => 2
  | .quaternions => 4
  | .octonions   => 8

theorem dim_reals       : dim .reals = 1 := rfl
theorem dim_complexes   : dim .complexes = 2 := rfl
theorem dim_quaternions : dim .quaternions = 4 := rfl
theorem dim_octonions   : dim .octonions = 8 := rfl

/-- The list of dimensions agrees with the per-algebra `dim`. -/
theorem divAlgDims_eq_dims :
    divAlgDims = [dim .reals, dim .complexes, dim .quaternions, dim .octonions] := rfl

-- ══════════════════════════════════════════════════════════
-- EACH DIMENSION IS A POWER OF TWO  (1,2,4,8 = 2^0,2^1,2^2,2^3)
-- ══════════════════════════════════════════════════════════

theorem dim_reals_pow       : dim .reals = 2 ^ 0 := by decide
theorem dim_complexes_pow   : dim .complexes = 2 ^ 1 := by decide
theorem dim_quaternions_pow : dim .quaternions = 2 ^ 2 := by decide
theorem dim_octonions_pow   : dim .octonions = 2 ^ 3 := by decide

/-- Every entry of `divAlgDims` is the corresponding power of two `2^k`. -/
theorem divAlgDims_powers :
    divAlgDims[0]? = some (2 ^ 0) ∧ divAlgDims[1]? = some (2 ^ 1)
    ∧ divAlgDims[2]? = some (2 ^ 2) ∧ divAlgDims[3]? = some (2 ^ 3) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- **The dimension list is exactly `(List.range 4).map (2 ^ ·)`.** -/
theorem divAlgDims_eq_range_map :
    divAlgDims = (List.range 4).map (fun k => 2 ^ k) := by decide

-- ══════════════════════════════════════════════════════════
-- CAYLEY–DICKSON DOUBLING:  dimₙ₊₁ = 2 · dimₙ
-- ══════════════════════════════════════════════════════════

theorem double_R_to_C : dim .complexes   = 2 * dim .reals       := by decide
theorem double_C_to_H : dim .quaternions = 2 * dim .complexes   := by decide
theorem double_H_to_O : dim .octonions   = 2 * dim .quaternions := by decide

/-- **The full Cayley–Dickson doubling chain**: each algebra is twice the
    previous one — `2 = 2·1`, `4 = 2·2`, `8 = 2·4`. -/
theorem cayley_dickson_doubling_chain :
    dim .complexes = 2 * dim .reals
    ∧ dim .quaternions = 2 * dim .complexes
    ∧ dim .octonions = 2 * dim .quaternions := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- Doubling stated directly on the list: consecutive entries double. -/
theorem divAlgDims_consecutive_doubling :
    (∀ a ∈ divAlgDims.zip divAlgDims.tail, a.2 = 2 * a.1) := by decide

-- ══════════════════════════════════════════════════════════
-- TOTAL DIMENSION:  1 + 2 + 4 + 8 = 15 = 2^4 − 1
-- ══════════════════════════════════════════════════════════

/-- **The four dimensions sum to `15 = 2^4 − 1`** (the geometric series
    `2^0 + 2^1 + 2^2 + 2^3 = 2^4 − 1`). -/
theorem divAlgDims_sum_15 :
    divAlgDims.sum = 15 ∧ (15 : Nat) = 2 ^ 4 - 1 := by
  refine ⟨?_, ?_⟩ <;> decide

theorem divAlgDims_sum_eq_pow :
    divAlgDims.sum = 2 ^ 4 - 1 := by decide

-- ══════════════════════════════════════════════════════════
-- TIE TO THE FREUDENTHAL MAGIC SQUARE AND E₈
-- ══════════════════════════════════════════════════════════

/-- **`divAlgDims` is the magic-square indexing list** — equal to
    `FreudenthalMagicSquare.divDims = [1,2,4,8]`. -/
theorem divAlgDims_eq_freudenthal_divDims :
    divAlgDims = Gnosis.FreudenthalMagicSquare.divDims := rfl

/-- The largest algebra is the octonions, `dim 𝕆 = 8`, matching
    `OctavianCubicMagicSquare.octonionDim`. -/
theorem largest_is_octonion_dim :
    dim .octonions = 8 ∧ dim .octonions = Gnosis.OctavianCubicMagicSquare.octonionDim := by
  refine ⟨rfl, rfl⟩

/-- The last entry of `divAlgDims` is `8`, the octonion dimension, which indexes
    the exceptional (octonion) row of the Freudenthal square. -/
theorem divAlgDims_last_is_octonion :
    divAlgDims.getLastD 0 = 8
    ∧ divAlgDims.getLastD 0 = Gnosis.FreudenthalMagicSquare.divDims.getLastD 0 := by
  refine ⟨by decide, rfl⟩

/-- **The octonion row of the magic square tops out at E₈ (dim 248).** The
    largest Hurwitz dimension `8 = dim 𝕆` indexes the row
    `F₄(52) → E₆(78) → E₇(133) → E₈(248)`; its top entry is `dim E₈ = 248`. -/
theorem octonion_indexes_E8_row :
    dim .octonions = 8
    ∧ Gnosis.FreudenthalMagicSquare.cell 3 3 = 248
    ∧ Gnosis.OctavianCubicMagicSquare.lieAlgebraDim .E8 8 = 248 := by
  refine ⟨by decide, by decide, by decide⟩

-- ══════════════════════════════════════════════════════════
-- MASTER CERTIFICATE
-- ══════════════════════════════════════════════════════════

/-- **THE HURWITZ NORMED-DIVISION-ALGEBRA LADDER.** The four real normed
    division algebras ℝ, ℂ, ℍ, 𝕆 have dimensions `[1,2,4,8] = [2^0,2^1,2^2,2^3]`,
    obtained by Cayley–Dickson doubling (`2=2·1, 4=2·2, 8=2·4`); they sum to
    `15 = 2^4 − 1`; the dimension list equals `(range 4).map (2^·)` and equals
    `FreudenthalMagicSquare.divDims`; and the largest, `8 = dim 𝕆`, indexes the
    octonion row of the magic square whose top is `E₈` of dimension `248`.

    (Hurwitz's theorem — that these four are the ONLY such algebras — is cited in
    the module header, not formalized here.) -/
theorem hurwitz_division_algebra_ladder :
    -- dimensions and their power-of-two form
    divAlgDims = [1, 2, 4, 8]
    ∧ divAlgDims = (List.range 4).map (fun k => 2 ^ k)
    -- Cayley–Dickson doubling chain
    ∧ dim .complexes = 2 * dim .reals
    ∧ dim .quaternions = 2 * dim .complexes
    ∧ dim .octonions = 2 * dim .quaternions
    -- total = 15 = 2^4 - 1
    ∧ divAlgDims.sum = 15
    ∧ divAlgDims.sum = 2 ^ 4 - 1
    -- magic-square / E₈ tie-in
    ∧ divAlgDims = Gnosis.FreudenthalMagicSquare.divDims
    ∧ dim .octonions = Gnosis.OctavianCubicMagicSquare.octonionDim
    ∧ Gnosis.OctavianCubicMagicSquare.lieAlgebraDim .E8 8 = 248 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> first | rfl | decide

end Gnosis.HurwitzDivisionAlgebras
