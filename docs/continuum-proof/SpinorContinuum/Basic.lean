import Mathlib.Algebra.Quaternion
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Continuous SU(2) -> SO(3) double cover, Route A (unit quaternions by conjugation)

This Mathlib-enabled project is the CONTINUOUS LIFT of the discrete shadow proven (Init-only,
zero `sorry`) in `Gnosis.OrientationSpinorBridge` of the sovereign `gnosis-math` ledger. We do
NOT import across projects; we cite the discrete theorems by NAME in comments. The discrete
facts being lifted:

  * `Gnosis.OrientationSpinorBridge.square_loses_sign`     -- both sheets +1,-1 collapse to one
  * `Gnosis.OrientationSpinorBridge.squaring_is_double_cover` / `preimage_is_two` -- 2-elt fibre
  * `Gnosis.OrientationSpinorBridge.order_halves_under_quotient` -- sheet order 4, director order 2

The continuous carrier is the unit quaternions acting on the pure-imaginary 3-space `R^3` by
conjugation `rho q v = q * v * (star q)` (for unit `q`, `star q = q^{-1}`). We prove:

  (i)   HOMOMORPHISM           `rho 1 = id`, `rho (a*b) = rho a . rho b`   (the structural core)
  (ii)  KERNEL = {plus/minus 1} `rho q = id  <->  q = 1 or q = -1`        (the central win)
  (iii) PERIODICITY            `loop u (2pi) = -1`, `loop u (4pi) = 1`,
                               and `rho (loop u (2pi)) = id` (rotation back already at 2pi)

Surjectivity onto SO(3) (axis-angle) is left as an explicit `Next exploration:` obligation
(NO `sorry`). With surjectivity, `rho` descends to the genuine 2:1 cover SU(2) -> SO(3).

Naming discipline: this `rho` MAPS TO / IS THE CONTINUOUS LIFT OF the discrete shadow; it is
not asserted to BE it. A continuous/Real result legitimately pulls
`Classical.choice`/`propext`/`Quot.sound` via Mathlib; that is the whole point of quarantining
this away from the Init-only ledger. See `#print axioms` reports at the bottom.
-/

namespace SpinorContinuum

open Quaternion

/-- The real quaternions `ℍ[ℝ]`. -/
abbrev H := Quaternion ℝ

/-- A quaternion is PURE IMAGINARY when its real part is zero (the 3-space `R^3` spanned by
    i, j, k). The conjugation action restricts to this subspace. -/
def IsImag (v : H) : Prop := v.re = 0

/-- The conjugation action of a quaternion on a quaternion: `rho q v = q * v * star q`.
    For a UNIT quaternion (`normSq q = 1`), `star q = q⁻¹`, so this is genuine conjugation
    `q v q⁻¹`. This is the continuous lift of the discrete sheet-to-director projection. -/
noncomputable def rho (q v : H) : H := q * v * star q

-- ════════════════════════════════════════════════════════════════════
-- (i) HOMOMORPHISM  (expected-clean structural core)
-- ════════════════════════════════════════════════════════════════════

/-- `rho 1 = id`: the identity quaternion acts trivially. Continuous lift of the bridge's
    `toDirector_intertwines` identity component / `rho`-equivariance. -/
theorem rho_one (v : H) : rho 1 v = v := by
  simp [rho]

/-- `rho` is multiplicative: `rho (a*b) v = rho a (rho b v)`. This is the group-homomorphism
    property `Φ(ab) = Φ(a)∘Φ(b)`, from associativity and `star_mul`. Continuous lift of the
    equivariant quotient (`toDirector_intertwines`, `Φ_mul` in the skeleton §3). -/
theorem rho_mul (a b v : H) : rho (a * b) v = rho a (rho b v) := by
  simp only [rho, star_mul]
  noncomm_ring

-- ════════════════════════════════════════════════════════════════════
-- (ii) KERNEL = {plus/minus 1}  (the central win: continuous lift of `square_loses_sign`)
-- ════════════════════════════════════════════════════════════════════

/-- For a UNIT quaternion, `star q = q⁻¹` (`q * star q = normSq q = 1`). -/
theorem unit_mul_star {q : H} (h : normSq q = 1) : q * star q = 1 := by
  rw [Quaternion.self_mul_star, h, Quaternion.coe_one]

theorem unit_star_mul {q : H} (h : normSq q = 1) : star q * q = 1 := by
  rw [Quaternion.star_mul_self, h, Quaternion.coe_one]

/-- `rho (-1) = rho 1 = id`: BOTH `+1` and `-1` act as the identity rotation. THE SIGN IS
    LOST. This is the exact continuous lift of the discrete
    `Gnosis.OrientationSpinorBridge.square_loses_sign` (`square false = square true`): the
    two sheets `+1`, `-1` map to one director. The fibre over the identity rotation is the
    2-element set `{+1, -1}`. -/
theorem rho_neg_one (v : H) : rho (-1) v = v := by
  show (-1 : H) * v * star (-1 : H) = v
  have hs : star (-1 : H) = (-1 : H) := by
    apply Quaternion.ext <;> simp
  rw [hs, neg_one_mul v, neg_mul_comm, neg_neg, mul_one]

theorem rho_one_eq_rho_neg_one (v : H) : rho 1 v = rho (-1) v := by
  rw [rho_one, rho_neg_one]

/-- The basis imaginary quaternions i, j, k as quaternions. -/
def qI : H := ⟨0, 1, 0, 0⟩
def qJ : H := ⟨0, 0, 1, 0⟩
def qK : H := ⟨0, 0, 0, 1⟩

/-- A unit quaternion that acts trivially by conjugation on ALL of i, j, k must be `±1`.

    `rho q = id` means `q v = v q` for `v ∈ {i,j,k}` (using `rho q v = v` and right-multiplying
    by `q` via `star q * q = 1`), i.e. `q` commutes with i, j, k, hence lies in the center of
    `ℍ[ℝ]` = the real scalars; with `normSq q = 1` this forces `q = ±1`.

    This `{±1}` kernel IS the 2:1 double-cover property — the continuous statement whose
    discrete shadow is `Gnosis.OrientationSpinorBridge.squaring_is_double_cover` /
    `preimage_is_two` (the 2-element fibre). -/
theorem kernel_forces_pm_one {q : H} (h : normSq q = 1)
    (hi : rho q qI = qI) (hj : rho q qJ = qJ) (_hk : rho q qK = qK) :
    q = 1 ∨ q = -1 := by
  -- Turn `rho q v = v` (i.e. `q v star q = v`) into the commutation `q v = v q`,
  -- by right-multiplying by `q` and using `star q * q = 1`.
  have hsq : star q * q = 1 := unit_star_mul h
  have ci : q * qI = qI * q := by
    have hh := congrArg (· * q) hi
    simp only [rho] at hh
    -- (q * qI * star q) * q = qI * q  ⇒  q * qI = qI * q
    calc q * qI = q * qI * (star q * q) := by rw [hsq, mul_one]
      _ = q * qI * star q * q := by noncomm_ring
      _ = qI * q := hh
  have cj : q * qJ = qJ * q := by
    have hh := congrArg (· * q) hj
    simp only [rho] at hh
    calc q * qJ = q * qJ * (star q * q) := by rw [hsq, mul_one]
      _ = q * qJ * star q * q := by noncomm_ring
      _ = qJ * q := hh
  -- Read off coordinates of the commutation equations via the component `_mul` lemmas.
  -- ci  (commute with i=⟨0,1,0,0⟩) gives, in imJ and imK, the vanishing of imK and imJ.
  -- cj  (commute with j=⟨0,0,1,0⟩) gives, in imI, the vanishing of imI.
  have hk0 : q.imK = 0 := by
    have e := congrArg (fun w : H => w.imJ) ci
    simp only [qI, Quaternion.imJ_mul] at e
    linarith
  have hj0 : q.imJ = 0 := by
    have e := congrArg (fun w : H => w.imK) ci
    simp only [qI, Quaternion.imK_mul] at e
    linarith
  have hi0 : q.imI = 0 := by
    have e := congrArg (fun w : H => w.imK) cj
    simp only [qJ, Quaternion.imK_mul] at e
    linarith
  -- normSq = re^2 + imI^2 + imJ^2 + imK^2 = 1, with imag parts zero ⇒ re^2 = 1 ⇒ re = ±1
  have hns : q.re * q.re = 1 := by
    have hn := h
    simp only [Quaternion.normSq_def', hi0, hj0, hk0] at hn
    nlinarith [hn]
  have hre : q.re = 1 ∨ q.re = -1 := mul_self_eq_one_iff.mp hns
  rcases hre with hr | hr
  · left
    apply Quaternion.ext
    · simpa using hr
    · simpa using hi0
    · simpa using hj0
    · simpa using hk0
  · right
    apply Quaternion.ext
    · simpa using hr
    · simpa using hi0
    · simpa using hj0
    · simpa using hk0

/-- Conversely, both `+1` and `-1` are IN the kernel (act trivially). Together with
    `kernel_forces_pm_one` this pins the kernel to exactly `{+1, -1}`. -/
theorem pm_one_in_kernel (v : H) : rho 1 v = v ∧ rho (-1) v = v :=
  ⟨rho_one v, rho_neg_one v⟩

/-- **KERNEL = {±1}** (full characterization). For a unit quaternion `q`, `q` acts trivially
    on all three imaginary basis elements iff `q = 1` or `q = -1`. This is the continuous lift
    of the discrete 2:1 fibre `Gnosis.OrientationSpinorBridge.preimage_is_two`. -/
theorem kernel_eq_pm_one {q : H} (h : normSq q = 1) :
    (rho q qI = qI ∧ rho q qJ = qJ ∧ rho q qK = qK) ↔ (q = 1 ∨ q = -1) := by
  constructor
  · rintro ⟨hi, hj, hk⟩; exact kernel_forces_pm_one h hi hj hk
  · rintro (rfl | rfl)
    · exact ⟨rho_one _, rho_one _, rho_one _⟩
    · exact ⟨rho_neg_one _, rho_neg_one _, rho_neg_one _⟩

-- ════════════════════════════════════════════════════════════════════
-- (iii) PERIODICITY  (continuous lift of `order_halves_under_quotient`)
-- ════════════════════════════════════════════════════════════════════

/-- A one-parameter rotation about a FIXED unit axis. For an imaginary unit quaternion `u`
    (here we take the concrete axis `i = qI`), `loop t = cos(t/2) + sin(t/2)·i`. -/
noncomputable def loop (t : ℝ) : H := ⟨Real.cos (t / 2), Real.sin (t / 2), 0, 0⟩

/-- `loop 0 = 1`. -/
theorem loop_zero : loop 0 = 1 := by
  apply Quaternion.ext <;>
    simp [loop, Real.cos_zero, Real.sin_zero]

/-- `loop (2π) = -1`: the SPINOR has NOT returned after a 2π rotation — it has flipped sign.
    `cos π = -1`, `sin π = 0`. This is the continuous lift of the discrete
    `Gnosis.OrientationSpinorBridge.two_quanta_director_returns_sheet_flips`: two quanta (2π)
    flip the sheet. -/
theorem loop_two_pi : loop (2 * Real.pi) = -1 := by
  have ht : 2 * Real.pi / 2 = Real.pi := by ring
  apply Quaternion.ext <;>
    simp [loop, ht, Real.cos_pi, Real.sin_pi]

/-- `loop (4π) = 1`: the SPINOR returns only after a 4π rotation. `cos 2π = 1`, `sin 2π = 0`.
    Continuous lift of `Gnosis.OrientationSpinorBridge.four_quanta_sheet_returns` (four quanta
    return the sheet). -/
theorem loop_four_pi : loop (4 * Real.pi) = 1 := by
  have ht : 4 * Real.pi / 2 = 2 * Real.pi := by ring
  apply Quaternion.ext <;>
    simp [loop, ht, Real.cos_two_pi, Real.sin_two_pi]

/-- The loop is unit-norm at every time `t` (so it genuinely lands in the unit quaternions):
    `normSq (loop t) = cos²(t/2) + sin²(t/2) = 1`. -/
theorem loop_unit (t : ℝ) : normSq (loop t) = 1 := by
  simp only [loop, Quaternion.normSq_def']
  have := Real.sin_sq_add_cos_sq (t / 2)
  nlinarith [this]

/-- **The ROTATION returns already at 2π** while the spinor does not. `rho (loop (2π)) = id`
    because `loop (2π) = -1 ∈ ker`. So downstairs (rotation/director) the period is 2π;
    upstairs (spinor/sheet) the period is 4π. THE ORDER HALVES under the 2:1 quotient — the
    continuous lift of `Gnosis.OrientationSpinorBridge.order_halves_under_quotient`. -/
theorem rho_loop_two_pi (v : H) : rho (loop (2 * Real.pi)) v = v := by
  rw [loop_two_pi, rho_neg_one]

theorem rho_loop_four_pi (v : H) : rho (loop (4 * Real.pi)) v = v := by
  rw [loop_four_pi, rho_one]

/-- **PERIODICITY master statement** (continuous lift of `order_halves_under_quotient`).
    Upstairs the spinor loop has period 4π (`loop_two_pi = -1 ≠ 1`, `loop_four_pi = 1`);
    downstairs the rotation loop has period 2π (`rho_loop_two_pi = id`). -/
theorem spinor_4pi_vs_rotation_2pi :
    loop (2 * Real.pi) = -1
    ∧ loop (4 * Real.pi) = 1
    ∧ (∀ v : H, rho (loop (2 * Real.pi)) v = v)
    ∧ (∀ v : H, rho (loop (4 * Real.pi)) v = v) :=
  ⟨loop_two_pi, loop_four_pi, rho_loop_two_pi, rho_loop_four_pi⟩

-- ════════════════════════════════════════════════════════════════════
-- Master certificate: (i) + (ii) + (iii)
-- ════════════════════════════════════════════════════════════════════

/-- **SU(2) -> SO(3) CONTINUOUS COVER — proven core (i)+(ii)+(iii).**

    (i)   HOMOMORPHISM:  `rho 1 = id` and `rho (a*b) = rho a ∘ rho b`.
    (ii)  KERNEL = {±1}: for unit `q`, `rho q` fixes i,j,k  iff  `q = ±1` (sign lost — the
          continuous lift of `square_loses_sign`; 2-element fibre — lift of `preimage_is_two`).
    (iii) PERIODICITY:   `loop (2π) = -1` (spinor flipped) but `rho (loop (2π)) = id` (rotation
          returned); `loop (4π) = 1`. Order halves: 4π upstairs, 2π downstairs — the lift of
          `order_halves_under_quotient`.

    Surjectivity onto SO(3) (axis-angle) is the single deferred obligation; see the
    `Next exploration:` note. With it, `rho` descends to the genuine 2:1 cover. -/
theorem su2_so3_continuous_cover_core :
    -- (i) homomorphism
    ((∀ v : H, rho 1 v = v) ∧ (∀ a b v : H, rho (a * b) v = rho a (rho b v)))
    -- (ii) kernel = {±1} for unit quaternions
    ∧ (∀ q : H, normSq q = 1 →
        ((rho q qI = qI ∧ rho q qJ = qJ ∧ rho q qK = qK) ↔ (q = 1 ∨ q = -1)))
    -- (iii) periodicity: spinor 4π, rotation 2π
    ∧ (loop (2 * Real.pi) = -1 ∧ loop (4 * Real.pi) = 1
        ∧ (∀ v : H, rho (loop (2 * Real.pi)) v = v)
        ∧ (∀ v : H, rho (loop (4 * Real.pi)) v = v)) :=
  ⟨⟨rho_one, rho_mul⟩,
   fun _ h => kernel_eq_pm_one h,
   spinor_4pi_vs_rotation_2pi⟩

#print axioms su2_so3_continuous_cover_core

/-
Next exploration:
  (iv) SURJECTIVITY onto SO(3) — the single hard part deferred here (NOT a `sorry`). To
  complete the genuine cover one packages `rho q` (for unit `q`) as an element of
  `Matrix.specialOrthogonalGroup (Fin 3) ℝ` (orthogonality from `Quaternion.normSq_mul` /
  `map_mul`; `det = 1` from continuity + connectedness of the unit-quaternion group), giving
  a group hom `Φ : Spin(3) →* SO(3)` with `Φ.ker = {±1}` by `kernel_eq_pm_one`. Surjectivity
  is the axis-angle / Euler decomposition: every `R ∈ SO(3)` is a rotation by angle `θ` about
  a unit axis `u`, realized by `q = cos(θ/2) + sin(θ/2)·u` (generalizing `loop` from the fixed
  `i`-axis to an arbitrary unit imaginary `u`). Formalizing needs the eigenvalue-1 axis
  existence for `SO(3)` and an entrywise half-angle matrix identity. Until machine-checked, the
  cover here is "homomorphism with kernel {±1} onto its image"; surjectivity onto ALL of SO(3)
  remains the cited continuous picture. The discrete shadow
  `Gnosis.OrientationSpinorBridge.squaring_is_double_cover` is the π₀/order-2 image of this.
-/

end SpinorContinuum
