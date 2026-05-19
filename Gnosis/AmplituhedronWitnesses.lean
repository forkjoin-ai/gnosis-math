import Init
import Gnosis.AmplituhedronAttention
import Gnosis.AmplituhedronGrassmannian
import Gnosis.AmplituhedronVertices

-- Concrete witnesses that the Amplituhedron Attention theory is non-vacuous.
--
-- The Grassmannian and Vertices files define `IsPositive` and
-- `PositiveGrassmannian k d`, but a structure plus a predicate proves
-- nothing if no element ever satisfies the predicate. This file pins
-- down explicit Plücker-coordinate evaluations on small matrices and
-- computable-amplitude examples, all proved by `native_decide` —
-- the same tactic the rest of the gnosis-math kernel uses for
-- decidable closed-form equalities.
--
-- Init-only per the Rustic Church initiative.

namespace AmplituhedronAttention.Witnesses

open AmplituhedronAttention
open AmplituhedronAttention.Grassmannian
open AmplituhedronAttention.Vertices

-- ══════════════════════════════════════════════════════════
-- DETERMINANT — CONCRETE BASE CASES
-- ══════════════════════════════════════════════════════════

/-- 1×1 determinant evaluation: `det [[7]] = 7`. -/
theorem det_one_concrete : det [[(7 : Int)]] = (7 : Int) := by
  native_decide

/-- 2×2 determinant evaluation: `det [[2,3],[1,4]] = 5`. -/
theorem det_two_concrete :
    det [[(2 : Int), 3], [1, 4]] = 5 := by
  native_decide

/-- 3×3 determinant evaluation: `det [[1,0,0],[0,1,0],[0,0,1]] = 1`. -/
theorem det_three_identity :
    det [[(1 : Int), 0, 0], [0, 1, 0], [0, 0, 1]] = 1 := by
  native_decide

-- ══════════════════════════════════════════════════════════
-- POSITIVE GRASSMANNIAN — k=1 NON-VACUOUS WITNESS
-- ══════════════════════════════════════════════════════════

/-- The all-ones row of length d. -/
def onesRow (d : Nat) : List Int :=
  (List.range d).map (fun _ => (1 : Int))

theorem onesRow_length (d : Nat) :
    (onesRow d).length = d := by
  unfold onesRow
  rw [List.length_map]
  exact List.length_range

/-- The k=1 positive-Grassmannian candidate built from the all-ones row.
    A 1×d matrix [[1, 1, …, 1]] has every 1×1 minor equal to 1. -/
def onesPlane (d : Nat) : KPlane 1 d :=
  { rows := [onesRow d],
    rank_witness := rfl,
    width_witness := by
      intro row hrow
      cases hrow with
      | head => exact onesRow_length d
      | tail _ h => cases h }

/-- Concrete d=3 witness: every singleton-coord Plücker minor of
    `onesPlane 3` is exactly 1. -/
theorem onesPlane_3_plucker_0 : pluckerCoord (onesPlane 3) [0] = 1 := by
  native_decide

theorem onesPlane_3_plucker_1 : pluckerCoord (onesPlane 3) [1] = 1 := by
  native_decide

theorem onesPlane_3_plucker_2 : pluckerCoord (onesPlane 3) [2] = 1 := by
  native_decide

/-- Concrete witness: the Plücker vector of `onesPlane 3` is [1, 1, 1] —
    every coord strictly positive. Therefore Gr⁺(1, 3) is non-empty. -/
theorem onesPlane_3_plucker_vector :
    pluckerVector (onesPlane 3) = [1, 1, 1] := by
  native_decide

/-- The kSubsets enumeration for k=1, d=3 lists every singleton in
    reverse-lex order (recursive arm puts subsets containing d first). -/
theorem kSubsets_1_3 : kSubsets 1 3 = [[2], [1], [0]] := by
  native_decide

/-- Vertex count for Gr⁺(1, 3) is 3. -/
theorem vertexCount_1_3 : vertexCount 1 3 = 3 := by
  native_decide

-- ══════════════════════════════════════════════════════════
-- POSITIVE GRASSMANNIAN  Gr⁺(1, 3) IS NON-EMPTY
-- ══════════════════════════════════════════════════════════

/-- The Bool-decidable positivity check fires affirmatively on the
    all-ones plane in d=3. This is the headline non-vacuity theorem:
    Gr⁺(1, 3) contains the all-ones plane as a witness. -/
theorem onesPlane_3_isPositiveBool :
    isPositiveBool (onesPlane 3) = true := by
  native_decide

-- ══════════════════════════════════════════════════════════
-- BOUNDARY WITNESS — IDENTITY PLANE FROM STANDING WAVES
-- ══════════════════════════════════════════════════════════

/-- The 2×3 coordinate plane spanned by indices [0, 1] in 3-space.
    Plücker vector picks out exactly one nonzero coord (subset [0,1])
    and zeros on [0,2] and [1,2] — concrete boundary witness. -/
def coordPlane_2_3_01 : KPlane 2 3 :=
  coordinatePlane 2 3 [0, 1] rfl

theorem coordPlane_2_3_01_plucker_principal :
    pluckerCoord coordPlane_2_3_01 [0, 1] = 1 := by
  native_decide

theorem coordPlane_2_3_01_plucker_off_diag_02 :
    pluckerCoord coordPlane_2_3_01 [0, 2] = 0 := by
  native_decide

theorem coordPlane_2_3_01_plucker_off_diag_12 :
    pluckerCoord coordPlane_2_3_01 [1, 2] = 0 := by
  native_decide

/-- Concrete witness: the standing-wave coordinate plane lives on the
    boundary of Gr⁺(2, 3). Two of three Plücker coords vanish, so it
    is NOT in Gr⁺ — confirming the runtime perturbation step is needed. -/
theorem coordPlane_2_3_01_not_in_positive :
    isPositiveBool coordPlane_2_3_01 = false := by
  native_decide

-- ══════════════════════════════════════════════════════════
-- SCATTERING AMPLITUDE — CONCRETE EVALUATION
-- ══════════════════════════════════════════════════════════

/-- Bridge to `standingWaveToCoordinatePlane`: build a `StandingWaveDims`
    with k=2, indices=[0,1], and coverageDen=3 (i.e. 2/3 coverage),
    then exhibit the resulting plane's row matrix as exactly that of
    `coordPlane_2_3_01`. (We compare `.rows` because the structure
    has a Prop-valued `width_witness` and is not literally
    `DecidableEq`.) -/
def sampleStandingWave : StandingWaveDims :=
  { k := 2,
    indices := [0, 1],
    coverageNum := 2,
    coverageDen := 3 }

theorem sampleStandingWave_to_coordinatePlane :
    (standingWaveToCoordinatePlane sampleStandingWave (by rfl)).rows
      = coordPlane_2_3_01.rows := by
  native_decide

-- ══════════════════════════════════════════════════════════
-- VANDERMONDE WITNESS — Gr⁺(2, 4) IS NON-EMPTY
-- ══════════════════════════════════════════════════════════

/-- A Vandermonde-style 2×4 matrix: rows = (1, 2, 4, 8) and (1, 3, 9, 27).
    These are powers (2^k, 3^k) for k = 0..3. By the Vandermonde
    determinant formula, every 2×2 minor is strictly positive. -/
def vandermonde_2_4 : KPlane 2 4 :=
  { rows := [[1, 2, 4, 8], [1, 3, 9, 27]],
    rank_witness := rfl,
    width_witness := by
      intro row hrow
      cases hrow with
      | head => rfl
      | tail _ h =>
        cases h with
        | head => rfl
        | tail _ h' => cases h' }

/-- Concrete proof: every Plücker coord of `vandermonde_2_4` is > 0.
    The full Plücker vector evaluates to [36, 30, 19, 6, 5, 1]. -/
theorem vandermonde_2_4_plucker_vector :
    pluckerVector vandermonde_2_4 = [36, 30, 19, 6, 5, 1] := by
  native_decide

/-- The Vandermonde plane is in Gr⁺(2, 4): every Plücker coord > 0.
    This proves the positive Grassmannian is non-empty for k=2. -/
theorem vandermonde_2_4_isPositive :
    isPositiveBool vandermonde_2_4 = true := by
  native_decide

/-- Vertex count for Gr⁺(2, 4) is C(4,2) = 6, confirming the
    `kSubsets 2 4` enumeration. -/
theorem vertexCount_2_4 : vertexCount 2 4 = 6 := by
  native_decide

-- ══════════════════════════════════════════════════════════
-- AMPLITUDE EVALUATION ON THE VANDERMONDE WITNESS
-- ══════════════════════════════════════════════════════════

/-- Sample dual covector matching the Plücker vector length (6 entries).
    Picked positive so the amplitude is unambiguously positive. -/
def vandermonde_dual : List Int := [1, 1, 1, 1, 1, 1]

/-- Concrete scattering amplitude on the Vandermonde Gr⁺(2,4) witness:
    inner product of [36, 30, 19, 6, 5, 1] with the all-ones dual
    equals 36 + 30 + 19 + 6 + 5 + 1 = 97. The runtime layer can
    verify against this oracle. -/
theorem vandermonde_2_4_amplitude :
    let plucker := pluckerVector vandermonde_2_4
    (plucker.zip vandermonde_dual).foldl
      (fun acc p => acc + p.1 * p.2) 0
      = 97 := by
  native_decide

end AmplituhedronAttention.Witnesses
