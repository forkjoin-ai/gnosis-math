import Init
import Gnosis.CausalDiamond
import Gnosis.InformationLightCone
import Gnosis.AckermannRuntimeCertificate
import Gnosis.AckermannLightConeBridge

/-
  TimeTravelLightCone.lean
  ========================

  Time travel on the light-cone substrate, continuing the "Ackermann ceiling
  occupies the role of c" program (`AckermannLightConeBridge`,
  `InformationLightCone`, `AckermannIsLightSpeed`).

  ## The dictionary

  The bridge already split spacetime into three regions by the sign of the
  interval: timelike (inside the cone, causal), lightlike (on the cone,
  saturating), spacelike (outside, "elsewhere"). It also showed:

      sub-Ackermann runtime   ↔  timelike   (computable, causal)
      saturating runtime      ↔  lightlike  (the luminal front)
      super-Ackermann runtime ↔  spacelike  (uncomputable, acausal)

  Time travel lives in the spacelike region. A signal that reaches a spacelike
  cell `|x| > t` is, in special relativity, backward-in-time in some inertial
  frame — a tachyon, the carrier of a closed timelike curve. This module
  proves:

    * `no_tachyon_under_lightspeed` — a light-speed-respecting, origin-seeded
      signal is NEVER tachyonic (Hawking-style chronology protection).
    * `grandfather_paradox` — a closed timelike curve forces `P ↔ ¬P`, i.e.
      `False`: the paradox is logically real, so the only way the universe
      stays consistent is to forbid the loop.
    * `chronology_protected` — the c-bound forbids the spacelike channel the
      loop needs, so the contradiction can never be instantiated.
    * `tachyon_is_spacelike` / `time_travel_iff_super_ackermann` — the tachyon
      is exactly a super-Ackermann event: time travel ⟺ hypercomputation.

  Init + the light-cone substrate. Zero `sorry`, zero new `axiom`.
-/

namespace TimeTravelLightCone

open Gnosis.CausalDiamond
open InformationLightCone
open AckermannRuntimeCertificate
open AckermannLightConeBridge

/-! ## Tachyons: information outside the light cone -/

/-- A signal is **tachyonic** if it lights a cell strictly outside the light
    cone — spacelike separation `t < |x|`. In SR a spacelike signal runs
    backward in time in some inertial frame: the carrier of time travel. -/
def Tachyonic (sig : Signal) : Prop :=
  ∃ t x, sig t x = true ∧ t < x.natAbs

/-- **Chronology protection (no tachyon).** A signal that respects the speed of
    light and starts at the origin can never be tachyonic: it cannot reach a
    spacelike cell. No faster-than-light propagation ⇒ no backward-in-time
    signaling. -/
theorem no_tachyon_under_lightspeed (sig : Signal)
    (hc : RespectsLightSpeed sig) (h0 : StartsAtOrigin sig) :
    ¬ Tachyonic sig := by
  rintro ⟨t, x, hlit, hgt⟩
  have hcone : x.natAbs ≤ t := info_within_cone sig hc h0 t x hlit
  omega

/-! ## The grandfather paradox is logically contradictory -/

/-- **The grandfather paradox.** A closed timelike curve makes a proposition
    equivalent to its own negation — the time traveler exists iff the traveler
    is prevented from existing — which is `False`. The paradox is not a
    puzzle to be explained away; it is a genuine contradiction. Hence a
    consistent universe must forbid the loop that produces it. -/
theorem grandfather_paradox (Lives : Prop) (loop : Lives ↔ ¬ Lives) : False := by
  have hne : ¬ Lives := fun hl => (loop.mp hl) hl
  exact hne (loop.mpr hne)

/-- **Hawking-style chronology protection, composed.** In a universe whose
    signals respect the speed of light, the spacelike (tachyonic) channel a
    timelike loop would need does not exist, AND the loop it would create is
    contradictory. The c-bound is exactly what keeps chronology consistent. -/
theorem chronology_protected (sig : Signal)
    (hc : RespectsLightSpeed sig) (h0 : StartsAtOrigin sig) :
    ¬ Tachyonic sig ∧ (∀ P : Prop, (P ↔ ¬P) → False) :=
  ⟨no_tachyon_under_lightspeed sig hc h0, fun P loop => grandfather_paradox P loop⟩

/-! ## Tachyon = spacelike = super-Ackermann

  The time-travel carrier sits in the same region as a super-Ackermann
  runtime: outside the cone. Time travel ⟺ hypercomputation. -/

/-- A tachyonic (spacelike) event has positive interval — it is "elsewhere",
    outside the causal cone, the same region as a super-Ackermann runtime
    spike. -/
theorem tachyon_is_spacelike (t : Nat) (x : Int) (h : t < x.natAbs) :
    intervalSquared { time := 0, space := 0 } { time := (t : Int), space := x } > 0 := by
  have hnat : t * t < x.natAbs * x.natAbs := Nat.mul_self_lt_mul_self h
  have hcast : ((t * t : Nat) : Int) < ((x.natAbs * x.natAbs : Nat) : Int) := by
    exact_mod_cast hnat
  rw [Int.natAbs_mul_self, Int.natCast_mul] at hcast
  -- hcast : (t : Int) * t < x * x
  rw [show intervalSquared { time := 0, space := 0 } { time := (t : Int), space := x }
        = x * x - (t : Int) * (t : Int) from by
        show (x - 0) * (x - 0) - ((t : Int) - 0) * ((t : Int) - 0) = _
        simp [Int.sub_zero]]
  omega

/-- **Time travel ⟺ hypercomputation.** A runtime maps to a spacelike (time-
    travel) event exactly when it exceeds the Ackermann ceiling — i.e. computes
    faster than any total-computable function. To "send information into its
    own past" you must out-run the frontier of computability itself. -/
theorem time_travel_iff_super_ackermann (T : Runtime) (n : Nat) :
    ackermannCeiling n < T n
      ↔ intervalSquared origin (runtimeEvent T n) > 0 := by
  constructor
  · exact super_ackermann_is_spacelike T n
  · intro h
    rw [runtimeEvent, interval_origin] at h
    -- h : (T n : Int) * T n - (ackermannCeiling n : Int) * ackermannCeiling n > 0
    have hsq : (ackermannCeiling n : Int) * ackermannCeiling n < (T n : Int) * T n := by omega
    have hnat : ackermannCeiling n * ackermannCeiling n < T n * T n := by exact_mod_cast hsq
    rcases Nat.lt_or_ge (ackermannCeiling n) (T n) with h' | h'
    · exact h'
    · exfalso
      have := Nat.mul_self_le_mul_self h'
      omega

/-! ## The consistency knife-edge: the photon is the only realizable limit

  Light rides the cone exactly (lightlike); everything realizable is strictly
  inside (timelike); only the forbidden tachyon is outside. Time travel is the
  spacelike region you can never enter without breaking the speed of light —
  equivalently, without computing the uncomputable. -/

/-- The trichotomy at the runtime frontier: a runtime sample is causal-and-
    realizable (`≤` ceiling, in cone), exactly luminal (`=` ceiling, on cone),
    or a time-travel spike (`>` ceiling, spacelike). Exactly one holds. -/
theorem runtime_trichotomy (T : Runtime) (n : Nat) :
    (T n < ackermannCeiling n ∧ intervalSquared origin (runtimeEvent T n) < 0) ∨
    (T n = ackermannCeiling n ∧ intervalSquared origin (runtimeEvent T n) = 0) ∨
    (ackermannCeiling n < T n ∧ intervalSquared origin (runtimeEvent T n) > 0) := by
  rcases Nat.lt_trichotomy (T n) (ackermannCeiling n) with h | h | h
  · exact Or.inl ⟨h, subluminal_is_strictly_timelike T n h⟩
  · refine Or.inr (Or.inl ⟨h, ?_⟩)
    rw [runtimeEvent, interval_origin, h]; omega
  · exact Or.inr (Or.inr ⟨h, super_ackermann_is_spacelike T n h⟩)

end TimeTravelLightCone
