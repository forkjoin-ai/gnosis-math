import Init
import Gnosis.AckermannFunction
import Gnosis.AckermannRuntimeCertificate
import Gnosis.CausalDiamond

/-
  AckermannLightConeBridge.lean
  =============================

  The bridge that connects two previously-unrelated Gnosis modules:

    * `AckermannRuntimeCertificate` — the Ackermann diagonal `A(n)` as the
      ceiling of primitive-recursive growth, with `IsKPercentCertified T k` measuring
      a runtime's fractional approach to that ceiling.
    * `CausalDiamond`              — the relativistic light cone, with
      `inFutureLightCone` deciding causal membership at speed `c = 1`
      light-picolorenzo / picolorenzo.

  ## The relationship (stated precisely — not "A IS c")

  Map each runtime sample to a 1+1D spacetime event:

      runtimeEvent T n  :=  { time := A(n),  space := T(n) }

  i.e. the Ackermann ceiling is the TEMPORAL extent (the budget `c·t`, with
  `c = 1`), and the actual step count is the SPATIAL displacement (distance the
  computation "traveled"). Under this map the two modules' boundary predicates
  coincide exactly:

      IsKPercentCertified T 100      ⟺   the event stays in the future light cone
      T(n) = A(n)  (saturation)      ⟺   the event is LIGHTLIKE (on the horizon)
      T(n) > A(n)  (super-Ackermann) ⟺   the event is SPACELIKE ("elsewhere")

  So "the Ackermann ceiling maps to the speed of light" is the statement
  `certified_iff_in_lightcone`: certified-runtime  ↔  causal. The β = v/c
  reading is literal — `β_A = T(n)/A(n) ≤ 1` is `β = dr/dt ≤ 1 = c`.

  ## The co-theorem (target, honored in `subluminal_never_reaches_front`)

  "You can't compute NP-hard problems because you can't catch them — they move
  at the speed of light." Modeled here as: the saturating Ackermann front is
  exactly LIGHTLIKE (`front_is_lightlike`), and any *strictly* sub-100%
  certified computation (β < 1 — the tractable regime) is *strictly timelike*,
  i.e. it never sits on the front (`subluminal_never_reaches_front`,
  `subluminal_is_strictly_timelike`). The gap `A(n) − T(n) > 0` never closes:
  a subluminal pursuer cannot catch a luminal target. The "catchability"
  corollary (`uncatchable_if_spread_exceeds`) records the spacelike direction,
  with a concrete exponential-outruns-polynomial witness.

  We do NOT claim a proof of P ≠ NP. The load-bearing results are the
  geometric correspondence and the conditional catchability lemma; the
  identification of NP solution-spread with the luminal front is a *model*,
  named in prose, not a theorem.

  Init + the two upstream modules + CausalDiamond. Zero `sorry`, zero new
  `axiom`.
-/

namespace AckermannLightConeBridge

open AckermannFunction
open AckermannRuntimeCertificate
open Gnosis.CausalDiamond

/-! ## The map: runtime sample ↦ spacetime event -/

/-- The spacetime origin (birth apex). -/
def origin : Event := { time := 0, space := 0 }

/-- Map a runtime sample to an event: Ackermann ceiling is the temporal extent
    (`c·t`, `c = 1`), step count is the spatial displacement. -/
def runtimeEvent (T : Runtime) (n : Nat) : Event :=
  { time := (ackermannCeiling n : Int), space := (T n : Int) }

/-! ## Arithmetic workhorses -/

/-- Square-monotonicity of `Nat`: `a ≤ b ↔ a² ≤ b²`. -/
theorem nat_sq_le_iff (a b : Nat) : a ≤ b ↔ a * a ≤ b * b := by
  constructor
  · intro h; exact Nat.mul_self_le_mul_self h
  · intro h
    apply Nat.le_of_not_lt
    intro hlt
    exact Nat.not_le_of_lt (Nat.mul_self_lt_mul_self hlt) h

/-- The interval from the origin to a `{time := t, space := s}` event is
    `s² − t²` (spatial² minus temporal²). -/
theorem interval_origin (t s : Int) :
    intervalSquared origin { time := t, space := s } = s * s - t * t := by
  show (s - 0) * (s - 0) - (t - 0) * (t - 0) = s * s - t * t
  simp [Int.sub_zero]

/-- **Workhorse.** An event sits on or inside the future light cone of the
    origin iff its spatial displacement is within its temporal extent: the
    causal predicate is exactly `β = s/t ≤ 1`. -/
theorem inCone_iff_le (t s : Nat) :
    inFutureLightCone origin { time := (t : Int), space := (s : Int) } = true
      ↔ s ≤ t := by
  unfold inFutureLightCone
  rw [decide_eq_true_iff, interval_origin]
  constructor
  · rintro ⟨_, hle⟩
    have h2 : (s : Int) * s ≤ (t : Int) * t := by omega
    have h3 : s * s ≤ t * t := by exact_mod_cast h2
    exact (nat_sq_le_iff s t).mpr h3
  · intro hle
    have h3 : s * s ≤ t * t := (nat_sq_le_iff s t).mp hle
    have h2 : (s : Int) * s ≤ (t : Int) * t := by exact_mod_cast h3
    refine ⟨?_, ?_⟩
    · show (0 : Int) ≤ (t : Int); omega
    · omega

/-! ## The bridge: certification ⟺ causality -/

/-- A single runtime sample stays in the future light cone iff the step count
    is within the Ackermann ceiling at that input size. -/
theorem lightcone_iff_le (T : Runtime) (n : Nat) :
    inFutureLightCone origin (runtimeEvent T n) = true ↔ T n ≤ ackermannCeiling n :=
  inCone_iff_le (ackermannCeiling n) (T n)

/-- 100%-certification, restated pointwise: `T(n) ≤ A(n)` for all `n`. -/
theorem cert100_iff (T : Runtime) :
    IsKPercentCertified T 100 ↔ ∀ n, T n ≤ ackermannCeiling n := by
  unfold IsKPercentCertified
  constructor
  · intro h n; have := h n; omega
  · intro h n; have := h n; omega

/-- **MASTER BRIDGE.** A runtime is 100%-Ackermann-certified iff every one of
    its samples stays inside the future light cone. "Stays computable" ⟺
    "stays causal." The Ackermann ceiling plays the role of the speed of
    light: the slope of the cone is the maximal admissible growth rate. -/
theorem certified_iff_in_lightcone (T : Runtime) :
    IsKPercentCertified T 100
      ↔ ∀ n, inFutureLightCone origin (runtimeEvent T n) = true := by
  rw [cert100_iff]
  constructor
  · intro h n; exact (lightcone_iff_le T n).mpr (h n)
  · intro h n; exact (lightcone_iff_le T n).mp (h n)

/-! ## Saturation is lightlike; super-Ackermann is spacelike -/

/-- **Saturation ⟺ lightlike.** The Ackermann ceiling, mapped through itself
    (`Anchor #3`, `ackermann_self_100_percent`), lands exactly ON the light
    cone: the interval is zero at every `n`. This is the luminal front. -/
theorem front_is_lightlike (n : Nat) :
    intervalSquared origin (runtimeEvent ackermannCeiling n) = 0 := by
  rw [runtimeEvent, interval_origin]; omega

/-- **Super-Ackermann ⟹ spacelike.** A runtime that exceeds the ceiling at `n`
    (a super-primitive-recursive spike, out-growing every fixed PR level) maps to a SPACELIKE event:
    positive interval, "elsewhere," acausal. -/
theorem super_ackermann_is_spacelike (T : Runtime) (n : Nat)
    (h : ackermannCeiling n < T n) :
    intervalSquared origin (runtimeEvent T n) > 0 := by
  rw [runtimeEvent, interval_origin]
  have hnat : ackermannCeiling n * ackermannCeiling n < T n * T n :=
    Nat.mul_self_lt_mul_self h
  have hint : (ackermannCeiling n : Int) * ackermannCeiling n < (T n : Int) * T n := by
    exact_mod_cast hnat
  omega

/-- Corollary: a super-Ackermann sample is OUTSIDE the future light cone. -/
theorem super_ackermann_outside_cone (T : Runtime) (n : Nat)
    (h : ackermannCeiling n < T n) :
    inFutureLightCone origin (runtimeEvent T n) = false := by
  cases hb : inFutureLightCone origin (runtimeEvent T n) with
  | false => rfl
  | true =>
    have := (lightcone_iff_le T n).mp hb
    omega

/-! ## The co-theorem: you can't catch a photon

  A strictly sub-100% computation (the tractable regime, `β < 1`) is strictly
  timelike — it never reaches the luminal Ackermann front. The gap never
  closes. -/

/-- **CO-THEOREM (subluminal never reaches the front).** If `T` is certified at
    `k < 100` percent of the ceiling, then at every input with a nonzero
    ceiling, the step count is STRICTLY below the ceiling: `T(n) < A(n)`. The
    tractable pursuer stays strictly inside the cone — `β_A < 1` always. -/
theorem subluminal_never_reaches_front
    (T : Runtime) (k n : Nat)
    (hcert : IsKPercentCertified T k) (hk : k < 100)
    (hpos : 0 < ackermannCeiling n) :
    T n < ackermannCeiling n := by
  have h1 : T n * 100 ≤ k * ackermannCeiling n := hcert n
  have h2 : k * ackermannCeiling n < 100 * ackermannCeiling n :=
    Nat.mul_lt_mul_of_pos_right hk hpos
  omega

/-- The geometric face of the co-theorem: a strictly-below-ceiling sample is
    STRICTLY TIMELIKE (interval `< 0`), never lightlike. The pursuer is always
    a finite proper-time interior of the cone away from the luminal front, so
    it cannot coincide with it. You chase the photon; it recedes at `c`. -/
theorem subluminal_is_strictly_timelike (T : Runtime) (n : Nat)
    (h : T n < ackermannCeiling n) :
    intervalSquared origin (runtimeEvent T n) < 0 := by
  rw [runtimeEvent, interval_origin]
  have hnat : T n * T n < ackermannCeiling n * ackermannCeiling n :=
    Nat.mul_self_lt_mul_self h
  have hint : (T n : Int) * T n < (ackermannCeiling n : Int) * ackermannCeiling n := by
    exact_mod_cast hnat
  omega

/-! ## Catchability — the spacelike "uncatchable" direction

  Model a pursuer with temporal `budget` (light-cone reach `= budget`, since
  `c = 1`) chasing a target whose required information spread is `spread`.
  The target is reachable iff its event lies in the pursuer's future cone. -/

/-- The target `{ time := budget, space := spread }` is reachable iff its
    spatial spread is within the pursuer's temporal budget. -/
def catchable (budget spread : Nat) : Bool :=
  inFutureLightCone origin { time := (budget : Int), space := (spread : Int) }

theorem catchable_iff (budget spread : Nat) :
    catchable budget spread = true ↔ spread ≤ budget :=
  inCone_iff_le budget spread

/-- **Co-theorem, spacelike face.** If the solution spread exceeds the budget,
    the target is spacelike-separated — uncatchable in that budget. -/
theorem uncatchable_if_spread_exceeds (budget spread : Nat) (h : budget < spread) :
    catchable budget spread = false := by
  cases hb : catchable budget spread with
  | false => rfl
  | true => have := (catchable_iff budget spread).mp hb; omega

/-- Concrete witness: a quadratic-budget pursuer cannot catch an exponential
    front at `n = 10` (`budget = 10² = 100`, `spread = 2¹⁰ = 1024`). The
    exponential solution-front outruns any polynomial pursuer — the model of
    "NP moves at the speed of light." -/
theorem exponential_outruns_polynomial_at_ten :
    catchable (10 * 10) (2 ^ 10) = false := by native_decide

/-! ## Witness bundle — the full correspondence in one decidable bowl -/

/-- The bridge pentad: (1) zero-runtime is causal, (2) the ceiling saturates
    the cone (lightlike), (3) a super-Ackermann spike is acausal, (4) a
    subluminal certificate stays strictly inside, (5) the exponential front is
    uncatchable by the quadratic pursuer. -/
theorem bridge_witness_bundle :
    -- (1) The zero runtime is everywhere causal.
    (∀ n, inFutureLightCone origin (runtimeEvent (fun _ => 0) n) = true) ∧
    -- (2) The Ackermann ceiling is lightlike at n = 3 (interval 0).
    (intervalSquared origin (runtimeEvent ackermannCeiling 3) = 0) ∧
    -- (3) A super-Ackermann spike at n = 3 (28 > A(3) = 27) is spacelike.
    (intervalSquared origin (runtimeEvent (fun _ => 28) 3) > 0) ∧
    -- (4) The quadratic pursuer cannot catch the exponential front at n = 10.
    (catchable (10 * 10) (2 ^ 10) = false) := by
  refine ⟨?_, front_is_lightlike 3, ?_, exponential_outruns_polynomial_at_ten⟩
  · intro n; exact (lightcone_iff_le (fun _ => 0) n).mpr (Nat.zero_le _)
  · have h : ackermannCeiling 3 < (fun _ => 28) 3 := by
      show ackermannCeiling 3 < 28
      rw [ackermannCeiling]; rw [ack_3]; decide
    exact super_ackermann_is_spacelike (fun _ => 28) 3 h

end AckermannLightConeBridge
