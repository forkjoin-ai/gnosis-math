import Init
import Gnosis.InformationLightCone

/-
  InformationLightConeComplete.lean
  =================================

  Completeness companion to `InformationLightCone.info_within_cone`.

  `info_within_cone` is SOUNDNESS: a light-speed signal stays within `|x| ≤ t`.
  This module is COMPLETENESS: every cell with `|x| ≤ t` IS reachable by some
  light-speed, origin-seeded signal (`cone_complete`). Together they pin the
  reachable set to be EXACTLY the discrete light cone — so "maximum information
  speed = c" is tight, not merely an upper bound.

  The witness is the "walk-then-rest" signal: head straight toward the target
  at one cell per tick, then stop. Formally, at tick `t` it occupies the clamp
  of the target `x` into `[-t, t]`.

  Init + the light-cone substrate. Zero `sorry`, zero new `axiom`.
-/

namespace InformationLightConeComplete

open InformationLightCone

/-- Position of the walk-then-rest worldline aimed at `x`: the clamp of `x`
    into `[-t, t]`. -/
def clampPos (x : Int) (t : Nat) : Int := max (-(t : Int)) (min (t : Int) x)

/-- The signal that occupies `clampPos x t` at each tick `t`. -/
def reachSignal (x : Int) : Signal := fun t c => decide (c = clampPos x t)

theorem clampPos_zero (x : Int) : clampPos x 0 = 0 := by
  simp only [clampPos]; omega

theorem clampPos_step (x : Int) (t : Nat) :
    (clampPos x (t + 1) - clampPos x t).natAbs ≤ 1 := by
  simp only [clampPos]; omega

theorem clampPos_reaches (x : Int) (T : Nat) (h : x.natAbs ≤ T) :
    clampPos x T = x := by
  simp only [clampPos]; omega

/-- The walk-then-rest signal respects the speed of light. -/
theorem reachSignal_respects (x : Int) : RespectsLightSpeed (reachSignal x) := by
  intro t c hc
  simp only [reachSignal, decide_eq_true_iff] at hc
  have hstep := clampPos_step x t
  rw [← hc] at hstep
  -- hstep : (c - clampPos x t).natAbs ≤ 1
  rcases (show clampPos x t = c ∨ clampPos x t = c - 1 ∨ clampPos x t = c + 1 from by omega)
    with h | h | h
  · left; simp only [reachSignal, decide_eq_true_iff]; omega
  · right; left; simp only [reachSignal, decide_eq_true_iff]; omega
  · right; right; simp only [reachSignal, decide_eq_true_iff]; omega

/-- The walk-then-rest signal starts at the origin. -/
theorem reachSignal_starts (x : Int) : StartsAtOrigin (reachSignal x) := by
  intro c hc
  simp only [reachSignal, decide_eq_true_iff] at hc
  rw [clampPos_zero] at hc
  exact hc

/-- **COMPLETENESS.** Every cell inside the light cone (`|x| ≤ T`) is reachable
    by some light-speed, origin-seeded signal. Combined with
    `InformationLightCone.info_within_cone`, the reachable set is EXACTLY the
    discrete light cone: `c` is tight. -/
theorem cone_complete (T : Nat) (x : Int) (h : x.natAbs ≤ T) :
    ∃ sig, RespectsLightSpeed sig ∧ StartsAtOrigin sig ∧ sig T x = true := by
  refine ⟨reachSignal x, reachSignal_respects x, reachSignal_starts x, ?_⟩
  simp only [reachSignal, decide_eq_true_iff]
  rw [clampPos_reaches x T h]

/-- **Soundness + completeness, together.** A cell is reachable by SOME
    light-speed origin-seeded signal iff it lies within the light cone. The
    information cone is exactly `{ (t, x) : |x| ≤ t }`. -/
theorem reachable_iff_in_cone (T : Nat) (x : Int) :
    (∃ sig, RespectsLightSpeed sig ∧ StartsAtOrigin sig ∧ sig T x = true)
      ↔ x.natAbs ≤ T := by
  constructor
  · rintro ⟨sig, hc, h0, hlit⟩
    exact info_within_cone sig hc h0 T x hlit
  · exact cone_complete T x

end InformationLightConeComplete
