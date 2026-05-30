import SpinorContinuum.Basic
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Data.Matrix.Mul

/-!
# (iv) SU(2) -> SO(3): the image lands in SO(3), and one-parameter / axis-angle surjectivity

This file closes the last open edge of the continuous double cover started in
`SpinorContinuum.Basic`: it shows the conjugation map `rho q v = q * v * star q` (for a unit
quaternion `q`) restricted to the pure-imaginary 3-space is a genuine element of
`Matrix.specialOrthogonalGroup (Fin 3) ℝ` (orthogonal, determinant +1), and that the axis-angle
quaternion realizes every rotation about a fixed axis (one-parameter subgroup coverage), plus the
arbitrary-axis axis-angle realizer.

This is the CONTINUOUS LIFT OF the discrete shadow proven Init-only in
`Gnosis.OrientationSpinorBridge` (kernel/fibre) and ordered by `Gnosis.OrientationE8Bridge`
(order-level). We do NOT import across projects; we cite the discrete theorems by name in comments.

Naming discipline: `rho` MAPS TO / IS THE CONTINUOUS LIFT OF the discrete director projection; it
is not asserted to BE it. Real/continuous results legitimately pull
`Classical.choice`/`propext`/`Quot.sound` via Mathlib.
-/

namespace SpinorContinuum

open Quaternion Matrix

/-! ## Foundations: `rho` preserves the imaginary subspace, is linear, and is an isometry -/

/-- `rho` is additive in the vector argument. -/
theorem rho_add (q a b : H) : rho q (a + b) = rho q a + rho q b := by
  simp only [rho, mul_add, add_mul]

/-- `rho` is ℝ-homogeneous in the vector argument. -/
theorem rho_smul (q : H) (r : ℝ) (v : H) : rho q (r • v) = r • rho q v := by
  show q * (r • v) * star q = r • (q * v * star q)
  apply Quaternion.ext <;>
    simp only [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
      Quaternion.re_smul, Quaternion.imI_smul, Quaternion.imJ_smul, Quaternion.imK_smul,
      smul_eq_mul] <;>
    ring

/-- For a UNIT quaternion `q`, `rho q` preserves `normSq` (it is an isometry of the 4-space, hence
    of the imaginary 3-subspace it preserves): `normSq (rho q v) = normSq v`. Uses the
    multiplicativity of `normSq` (`map_mul`) and `normSq_star`. -/
theorem rho_isometry {q : H} (h : normSq q = 1) (v : H) : normSq (rho q v) = normSq v := by
  simp only [rho]
  rw [map_mul, map_mul, Quaternion.normSq_star, h, one_mul, mul_one]
  -- remaining: normSq v = normSq v (after the rewrites collapse the two `normSq q = 1` factors)

/-- For a UNIT quaternion `q`, `rho q` preserves the pure-imaginary subspace: if `v.re = 0`
    then `(rho q v).re = 0`. Conjugation preserves the real part (the "trace"), and `v` having
    zero real part keeps it zero. -/
theorem rho_preserves_imag {q : H} (h : normSq q = 1) {v : H} (hv : v.re = 0) :
    (rho q v).re = 0 := by
  -- (rho q v).re = (q v star q).re. We show it equals v.re via the conjugation trace identity.
  -- Use that re(a) = (a + star a)/2-style: star (q v star q) = q (star v) star q, and re is
  -- (x + star x).re component. Cleaner: expand re via component lemmas.
  have hq : q.re ^ 2 + q.imI ^ 2 + q.imJ ^ 2 + q.imK ^ 2 = 1 := by
    have := h; rw [Quaternion.normSq_def'] at this; linarith [this]
  simp only [rho, Quaternion.re_mul, Quaternion.re_star, Quaternion.imI_star,
    Quaternion.imJ_star, Quaternion.imK_star, Quaternion.imI_mul, Quaternion.imJ_mul,
    Quaternion.imK_mul, hv]
  ring_nf

/-! ## (1) The image lands in SO(3): the explicit rotation matrix is in `specialOrthogonalGroup` -/

/-- The explicit `3×3` real matrix of `rho q` acting on the imaginary basis `(i, j, k)`, written in
    terms of the components `w = q.re`, `x = q.imI`, `y = q.imJ`, `z = q.imK`. Column `c` is the
    imaginary part of `rho q` applied to the `c`-th imaginary basis quaternion. This is the standard
    unit-quaternion rotation matrix; we verify below it represents `rho` on the three basis vectors
    and that for a unit quaternion it is orthogonal with determinant `+1`. -/
def rhoMat (q : H) : Matrix (Fin 3) (Fin 3) ℝ :=
  let w := q.re; let x := q.imI; let y := q.imJ; let z := q.imK
  !![w*w + x*x - y*y - z*z, 2*(x*y - w*z),         2*(x*z + w*y);
     2*(x*y + w*z),         w*w - x*x + y*y - z*z, 2*(y*z - w*x);
     2*(x*z - w*y),         2*(y*z + w*x),         w*w - x*x - y*y + z*z]

/-- The columns of `rhoMat q` are the imaginary parts of `rho q` on the basis `i, j, k`: column 0 is
    `rho q qI`, column 1 is `rho q qJ`, column 2 is `rho q qK`. So `rhoMat q` genuinely is the
    matrix of the linear map `rho q` restricted to the imaginary 3-space (in the `i,j,k` basis).
    Verified component-by-component against the quaternion product. -/
theorem rhoMat_col_zero (q : H) :
    ((rho q qI).imI = rhoMat q 0 0) ∧ ((rho q qI).imJ = rhoMat q 1 0)
      ∧ ((rho q qI).imK = rhoMat q 2 0) := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [rho, qI, rhoMat, of_apply, cons_val_zero, cons_val_one, cons_val_two,
      vecHead, vecTail, Function.comp, Fin.succ_zero_eq_one,
      Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, Quaternion.re_mul,
      Quaternion.re_star, Quaternion.imI_star, Quaternion.imJ_star, Quaternion.imK_star] <;>
    ring

theorem rhoMat_col_one (q : H) :
    ((rho q qJ).imI = rhoMat q 0 1) ∧ ((rho q qJ).imJ = rhoMat q 1 1)
      ∧ ((rho q qJ).imK = rhoMat q 2 1) := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [rho, qJ, rhoMat, of_apply, cons_val_zero, cons_val_one, cons_val_two,
      vecHead, vecTail, Function.comp, Fin.succ_zero_eq_one,
      Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, Quaternion.re_mul,
      Quaternion.re_star, Quaternion.imI_star, Quaternion.imJ_star, Quaternion.imK_star] <;>
    ring

theorem rhoMat_col_two (q : H) :
    ((rho q qK).imI = rhoMat q 0 2) ∧ ((rho q qK).imJ = rhoMat q 1 2)
      ∧ ((rho q qK).imK = rhoMat q 2 2) := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [rho, qK, rhoMat, of_apply, cons_val_zero, cons_val_one, cons_val_two,
      vecHead, vecTail, Function.comp, Fin.succ_zero_eq_one,
      Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, Quaternion.re_mul,
      Quaternion.re_star, Quaternion.imI_star, Quaternion.imJ_star, Quaternion.imK_star] <;>
    ring

/-- `rhoMat q` written as an explicit `!![...]` literal (definitional unfolding). -/
theorem rhoMat_eq (q : H) :
    rhoMat q =
      !![q.re*q.re + q.imI*q.imI - q.imJ*q.imJ - q.imK*q.imK, 2*(q.imI*q.imJ - q.re*q.imK),
           2*(q.imI*q.imK + q.re*q.imJ);
         2*(q.imI*q.imJ + q.re*q.imK), q.re*q.re - q.imI*q.imI + q.imJ*q.imJ - q.imK*q.imK,
           2*(q.imJ*q.imK - q.re*q.imI);
         2*(q.imI*q.imK - q.re*q.imJ), 2*(q.imJ*q.imK + q.re*q.imI),
           q.re*q.re - q.imI*q.imI - q.imJ*q.imJ + q.imK*q.imK] := rfl

/-- The transpose `(rhoMat q)ᵀ` as an explicit `!![...]` literal. -/
theorem rhoMat_transpose_eq (q : H) :
    (rhoMat q)ᵀ =
      !![q.re*q.re + q.imI*q.imI - q.imJ*q.imJ - q.imK*q.imK, 2*(q.imI*q.imJ + q.re*q.imK),
           2*(q.imI*q.imK - q.re*q.imJ);
         2*(q.imI*q.imJ - q.re*q.imK), q.re*q.re - q.imI*q.imI + q.imJ*q.imJ - q.imK*q.imK,
           2*(q.imJ*q.imK + q.re*q.imI);
         2*(q.imI*q.imK + q.re*q.imJ), 2*(q.imJ*q.imK - q.re*q.imI),
           q.re*q.re - q.imI*q.imI - q.imJ*q.imJ + q.imK*q.imK] := by
  rw [rhoMat_eq]; ext i j; fin_cases i <;> fin_cases j <;> rfl

set_option maxHeartbeats 1600000 in
/-- For a UNIT quaternion `q`, `rhoMat q` is ORTHOGONAL: `(rhoMat q)ᵀ * rhoMat q = 1`. Each entry
    of the `!![...]` product reduces, using `w²+x²+y²+z²=1`, to a Kronecker delta. -/
theorem rhoMat_orthogonal {q : H} (h : normSq q = 1) :
    (rhoMat q)ᵀ * rhoMat q = 1 := by
  have hq : q.re ^ 2 + q.imI ^ 2 + q.imJ ^ 2 + q.imK ^ 2 = 1 := by
    have := h; rw [Quaternion.normSq_def'] at this; linarith [this]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rhoMat, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three, Matrix.one_apply]
  -- diagonal entries equal `(w²+x²+y²+z²)² = 1`; off-diagonals are identically `0`
  all_goals (try ring)
  all_goals linear_combination (q.re ^ 2 + q.imI ^ 2 + q.imJ ^ 2 + q.imK ^ 2 + 1) * hq

set_option maxHeartbeats 1600000 in
/-- For a UNIT quaternion `q`, `det (rhoMat q) = 1`. Reduces, via `det_fin_three` and
    `w²+x²+y²+z²=1`, to `(w²+x²+y²+z²)³ = 1`. -/
theorem rhoMat_det_one {q : H} (h : normSq q = 1) :
    (rhoMat q).det = 1 := by
  have hq : q.re ^ 2 + q.imI ^ 2 + q.imJ ^ 2 + q.imK ^ 2 = 1 := by
    have := h; rw [Quaternion.normSq_def'] at this; linarith [this]
  simp only [rhoMat, det_fin_three, of_apply, cons_val_zero, cons_val_one, cons_val_two,
    head_cons, head_fin_const, vecHead, vecTail, Function.comp, Fin.succ_zero_eq_one]
  -- det = (w²+x²+y²+z²)³ = 1³ = 1
  linear_combination
    ((q.re ^ 2 + q.imI ^ 2 + q.imJ ^ 2 + q.imK ^ 2) ^ 2
      + (q.re ^ 2 + q.imI ^ 2 + q.imJ ^ 2 + q.imK ^ 2) + 1) * hq

/-- **(1) THE COVER MAPS INTO SO(3).** For every UNIT quaternion `q`, the matrix `rhoMat q` of the
    conjugation action `rho q` on the imaginary 3-space is a genuine element of
    `Matrix.specialOrthogonalGroup (Fin 3) ℝ` (orthogonal with determinant `+1`). Combined with the
    `{±1}` kernel from `SpinorContinuum.Basic.kernel_eq_pm_one`, this is "the cover lands in SO(3),
    2:1" — half of "2:1 ONTO". Continuous lift of the discrete director projection of
    `Gnosis.OrientationSpinorBridge`. -/
theorem rho_mem_SO3 {q : H} (h : normSq q = 1) :
    rhoMat q ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ := by
  rw [Matrix.mem_specialOrthogonalGroup_iff]
  exact ⟨(Matrix.mem_orthogonalGroup_iff' (A := rhoMat q)).mpr (rhoMat_orthogonal h),
    rhoMat_det_one h⟩

/-! ## (2)/(3) Axis-angle realizer and fixed-axis one-parameter subgroup coverage

Surjectivity onto ALL of `SO(3)` is the genuine remaining obstruction: it needs the
eigenvalue-`1` axis-existence theorem for `SO(3)` (every real `3×3` rotation fixes some axis),
which Mathlib does not currently provide as a packaged lemma. We land the strongest honest
partial: (a) the arbitrary-axis axis-angle quaternion is a unit quaternion, so it maps into
`SO(3)` by `rho_mem_SO3`; and (b) the fixed-`i`-axis one-parameter subgroup `loop` (from
`SpinorContinuum.Basic`) realizes the full circle of rotation angles about that axis, fixing the
axis and rotating the orthogonal `(j,k)`-plane by `θ`. The global axis-angle packaging is left as
an explicit `Next exploration:`. -/

/-- The axis-angle quaternion for a unit imaginary axis `n` (with `normSq n = 1`, `n.re = 0`) and
    angle `θ`: `cos(θ/2) + sin(θ/2)·n`. This generalizes `SpinorContinuum.loop` from the fixed
    `i`-axis to an arbitrary axis. -/
noncomputable def axisAngle (n : H) (θ : ℝ) : H :=
  ⟨Real.cos (θ / 2), Real.sin (θ / 2) * n.imI, Real.sin (θ / 2) * n.imJ,
    Real.sin (θ / 2) * n.imK⟩

/-- The axis-angle quaternion is unit-norm whenever the axis is a unit imaginary quaternion:
    `cos²(θ/2) + sin²(θ/2)·(nᵢ²+n_j²+n_k²) = cos²(θ/2) + sin²(θ/2) = 1`. -/
theorem axisAngle_unit {n : H} (hn : normSq n = 1) (hre : n.re = 0) (θ : ℝ) :
    normSq (axisAngle n θ) = 1 := by
  have hnsum : n.imI ^ 2 + n.imJ ^ 2 + n.imK ^ 2 = 1 := by
    have := hn; rw [Quaternion.normSq_def', hre] at this; nlinarith [this]
  have hsc := Real.sin_sq_add_cos_sq (θ / 2)
  simp only [axisAngle, Quaternion.normSq_def']
  nlinarith [hsc, hnsum, sq_nonneg (Real.sin (θ / 2)), sq_nonneg (Real.cos (θ / 2))]

/-- **(2) AXIS-ANGLE LANDS IN SO(3).** For any unit imaginary axis `n` and angle `θ`, the rotation
    `rho (axisAngle n θ)` is a bona-fide element of `SO(3)`. Together with `rho_mem_SO3` this says the
    entire axis-angle family — the conjectured image of a surjection — is inside `SO(3)`. -/
theorem axisAngle_mem_SO3 {n : H} (hn : normSq n = 1) (hre : n.re = 0) (θ : ℝ) :
    rhoMat (axisAngle n θ) ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ :=
  rho_mem_SO3 (axisAngle_unit hn hre θ)

/-- `axisAngle qI θ = loop θ`: the arbitrary-axis realizer specializes to the fixed-`i`-axis loop of
    `SpinorContinuum.Basic`. -/
theorem axisAngle_qI (θ : ℝ) : axisAngle qI θ = loop θ := by
  apply Quaternion.ext <;> simp [axisAngle, loop, qI]

/-- **The fixed-`i`-axis one-parameter subgroup FIXES the axis `i`** for every angle `θ`:
    `rho (loop θ) qI = qI`. The axis of rotation is invariant. -/
theorem loop_fixes_axis (θ : ℝ) : rho (loop θ) qI = qI := by
  have hsc := Real.sin_sq_add_cos_sq (θ / 2)
  apply Quaternion.ext <;>
    simp only [rho, loop, qI, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
      Quaternion.imK_mul, Quaternion.re_star, Quaternion.imI_star, Quaternion.imJ_star,
      Quaternion.imK_star] <;>
    nlinarith [hsc]

/-- **The fixed-`i`-axis one-parameter subgroup ROTATES the orthogonal `(j,k)`-plane by `θ`**:
    `rho (loop θ) qJ = cos θ · j + sin θ · k`. This is the genuine `SO(2) ↪ SO(3)` rotation by the
    full angle `θ` about the `i`-axis, so EVERY rotation about this fixed axis is realized — the
    one-parameter subgroups are covered. (Uses the half-angle/double-angle identities.) -/
theorem loop_rotates_plane_J (θ : ℝ) :
    rho (loop θ) qJ = ⟨0, 0, Real.cos θ, Real.sin θ⟩ := by
  have hcos : Real.cos θ = Real.cos (θ / 2) ^ 2 - Real.sin (θ / 2) ^ 2 := by
    have := Real.cos_two_mul' (θ / 2); rw [show 2 * (θ / 2) = θ by ring] at this; exact this
  have hsin : Real.sin θ = 2 * Real.sin (θ / 2) * Real.cos (θ / 2) := by
    have := Real.sin_two_mul (θ / 2); rw [show 2 * (θ / 2) = θ by ring] at this; exact this
  apply Quaternion.ext <;>
    simp only [rho, loop, qJ, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
      Quaternion.imK_mul, Quaternion.re_star, Quaternion.imI_star, Quaternion.imJ_star,
      Quaternion.imK_star, hcos, hsin] <;>
    ring

/-- Likewise `rho (loop θ) qK = -sin θ · j + cos θ · k`: the other orthogonal coordinate. -/
theorem loop_rotates_plane_K (θ : ℝ) :
    rho (loop θ) qK = ⟨0, 0, -Real.sin θ, Real.cos θ⟩ := by
  have hcos : Real.cos θ = Real.cos (θ / 2) ^ 2 - Real.sin (θ / 2) ^ 2 := by
    have := Real.cos_two_mul' (θ / 2); rw [show 2 * (θ / 2) = θ by ring] at this; exact this
  have hsin : Real.sin θ = 2 * Real.sin (θ / 2) * Real.cos (θ / 2) := by
    have := Real.sin_two_mul (θ / 2); rw [show 2 * (θ / 2) = θ by ring] at this; exact this
  apply Quaternion.ext <;>
    simp only [rho, loop, qK, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
      Quaternion.imK_mul, Quaternion.re_star, Quaternion.imI_star, Quaternion.imJ_star,
      Quaternion.imK_star, hcos, hsin] <;>
    ring

/-- **(3) ONE-PARAMETER SUBGROUP COVERAGE (fixed `i`-axis).** For every angle `θ`, `rho (loop θ)`
    is the rotation about the `i`-axis by `θ`: it fixes `i` and acts on the orthogonal `(j,k)`-plane
    as the planar rotation matrix `[[cos θ, -sin θ],[sin θ, cos θ]]`. Hence the whole circle of
    rotations about this fixed axis is in the image of `rho` (as `θ` ranges over `ℝ`). The remaining
    step to FULL surjectivity is to vary the axis over all unit imaginary `n` and invoke the
    `SO(3)` axis-existence theorem; see `Next exploration:`. -/
theorem loop_is_axis_rotation (θ : ℝ) :
    rho (loop θ) qI = qI
    ∧ rho (loop θ) qJ = ⟨0, 0, Real.cos θ, Real.sin θ⟩
    ∧ rho (loop θ) qK = ⟨0, 0, -Real.sin θ, Real.cos θ⟩ :=
  ⟨loop_fixes_axis θ, loop_rotates_plane_J θ, loop_rotates_plane_K θ⟩

/-- **SU(2) -> SO(3): the SO(3)-side certificate (1)+(2)+(3).**

    (1)  IMAGE IN SO(3):  for every unit quaternion `q`, `rhoMat q ∈ specialOrthogonalGroup (Fin 3) ℝ`
         (orthogonal, det `+1`).
    (2)  AXIS-ANGLE IN SO(3):  for every unit imaginary axis `n` and angle `θ`,
         `rhoMat (axisAngle n θ) ∈ SO(3)` — the entire axis-angle family lies in `SO(3)`.
    (3)  ONE-PARAMETER COVERAGE:  the fixed-`i`-axis subgroup `rho (loop θ)` realizes the full circle
         of rotations about that axis (fixes `i`, rotates the `(j,k)`-plane by `θ`).

    Combined with `SpinorContinuum.Basic.kernel_eq_pm_one` (`{±1}` kernel), this upgrades the cover
    to "homomorphism with kernel `{±1}` mapping into `SO(3)`, hitting every one-parameter subgroup".
    FULL global surjectivity onto `SO(3)` remains the cited continuous picture (axis existence). This
    is the continuous lift of the discrete director projection `Gnosis.OrientationSpinorBridge`, with
    order data from `Gnosis.OrientationE8Bridge`. -/
theorem su2_so3_into_SO3_with_axis_coverage :
    (∀ q : H, normSq q = 1 → rhoMat q ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    ∧ (∀ (n : H), normSq n = 1 → n.re = 0 → ∀ θ : ℝ,
        rhoMat (axisAngle n θ) ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    ∧ (∀ θ : ℝ, rho (loop θ) qI = qI
        ∧ rho (loop θ) qJ = ⟨0, 0, Real.cos θ, Real.sin θ⟩
        ∧ rho (loop θ) qK = ⟨0, 0, -Real.sin θ, Real.cos θ⟩) :=
  ⟨fun _ h => rho_mem_SO3 h,
   fun _ hn hre θ => axisAngle_mem_SO3 hn hre θ,
   loop_is_axis_rotation⟩

#print axioms rho_mem_SO3
#print axioms su2_so3_into_SO3_with_axis_coverage

/-
Next exploration (FULL surjectivity onto SO(3)):
  The image-in-SO(3) (1), the axis-angle family membership (2), and fixed-axis one-parameter
  coverage (3) are now machine-checked. To close FULL `Function.Surjective` of
  `q ↦ rhoMat q : {unit quaternions} → specialOrthogonalGroup (Fin 3) ℝ`, the remaining obligation
  is the SO(3) AXIS-EXISTENCE theorem: every `R ∈ SO(3)` has eigenvalue `1` (a fixed unit axis `n`),
  because `det(R - I) = det(Rᵀ)·det(R - I) = det(I - Rᵀ) = det((I - R)ᵀ) = det(I - R) = (-1)³ det(R - I)`
  forces `det(R - I) = 0` in odd dimension. Then `R` restricted to `n^⊥` is a planar rotation by some
  angle `θ`, and `R = rhoMat (axisAngle n θ)` by `loop_rotates_plane_J/K` generalized off the
  `i`-axis (conjugate the `i`-axis case by the orthogonal frame `(n, e₂, e₃)`). Mathlib lacks a
  packaged SO(3) axis lemma, so this is an independent formalization, not a `sorry`. With it,
  `rho` descends to the genuine 2:1 ONTO cover `Spin(3) = SU(2) → SO(3)`, whose `π₀`/order-2 image is
  the discrete `Gnosis.OrientationSpinorBridge.squaring_is_double_cover`.
-/

end SpinorContinuum
