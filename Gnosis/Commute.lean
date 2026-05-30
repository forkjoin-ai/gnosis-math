/-!
# Commute — the LIVING CITY breathes (home by night, work by day)

A civic agent commutes between its claimed HOME floor (night) and its WORKPLACE
business (day), driven by the SUN. The schedule is the deterministic map

    altitude ↦ workFraction ∈ [0,1]   (here scaled to permille [0,1000] over ℤ)

`workFraction` is the fraction of the way an agent has travelled from home to its
workplace. We prove the schedule is:

  * TOTAL — defined for every solar altitude (it is a plain `Int → Int`);
  * BOUNDED — always in `[0,1000]` permille (never past the workplace, never
    behind home);
  * MONOTONE non-decreasing in the altitude — so a worker rises toward work as
    the sun rises and falls back home as it sets, with no flicker;
  * CONTIGUOUS daytime — the set of altitudes at which the agent is fully at work
    is the single up-closed interval `altitude ≥ dayAlt`, and the set at which it
    is fully home is the single down-closed interval `altitude ≤ nightAlt`. A
    worker is therefore at work for exactly one contiguous daytime interval.

This matches `apps/monster-studio/src/scene/cave-scene.ts`:`commuteWorkFraction`,
which the renderer reads each tick to lerp the agent between its claimed home
floor and its occupation building (no `Math.sin`, no randomness).

Init-only, no Mathlib. The arithmetic is over `ℤ` with division by the literal
band width, which `omega` discharges directly. Expected axioms from
`#print axioms`: propext, Classical.choice, Quot.sound (no `sorry`, no custom
axioms).
-/

namespace Gnosis
namespace Commute

/-- Twilight band, in tenths of a degree of solar altitude.
    Below `nightAlt` the agent is fully home; above `dayAlt` fully at work. -/
def nightAlt : Int := -60   -- −6.0°
def dayAlt : Int := 60      --  +6.0°
def permille : Int := 1000  -- full-scale workFraction (= 1.0)
def bandWidth : Int := 120  -- dayAlt − nightAlt

theorem band_nonempty : nightAlt < dayAlt := by decide
theorem bandWidth_eq : bandWidth = dayAlt - nightAlt := by decide

/-- The commute schedule: solar altitude (tenths of a degree) ↦ workFraction in
    permille. A clamped linear ramp across the twilight band. TOTAL by typing.
    Division is by the literal `bandWidth = 120`, so `omega` reasons about it. -/
def workFraction (altitude : Int) : Int :=
  if altitude ≤ nightAlt then 0
  else if dayAlt ≤ altitude then permille
  else (altitude - nightAlt) * permille / bandWidth

/-- BOUNDED below: the agent never moves behind home. -/
theorem workFraction_nonneg (altitude : Int) : 0 ≤ workFraction altitude := by
  unfold workFraction nightAlt dayAlt permille bandWidth
  split
  · decide
  · split
    · decide
    · omega

/-- BOUNDED above: the agent never overshoots the workplace. -/
theorem workFraction_le_permille (altitude : Int) : workFraction altitude ≤ permille := by
  unfold workFraction nightAlt dayAlt permille bandWidth
  split
  · decide
  · split
    · exact Int.le_refl _
    · omega

/-- The interior ramp is monotone: dividing by the positive literal band width
    preserves order, and the linear numerator is monotone. -/
theorem ramp_monotone {a b : Int} (h : a ≤ b) :
    (a - nightAlt) * permille / bandWidth ≤ (b - nightAlt) * permille / bandWidth := by
  unfold nightAlt permille bandWidth
  apply Int.ediv_le_ediv (by decide)
  have : a - -60 ≤ b - -60 := by omega
  exact Int.mul_le_mul_of_nonneg_right this (by decide)

/-- MONOTONE: a higher sun never moves the agent backward. As the sun rises the
    agent rides smoothly toward work; as it sets, back home — no flicker. -/
theorem workFraction_monotone {a b : Int} (h : a ≤ b) :
    workFraction a ≤ workFraction b := by
  have hnonneg := workFraction_nonneg b
  unfold workFraction at hnonneg ⊢
  by_cases ha1 : a ≤ nightAlt
  · -- a is fully home (= 0) ≤ anything nonneg
    rw [if_pos ha1]; exact hnonneg
  · rw [if_neg ha1]
    by_cases ha2 : dayAlt ≤ a
    · -- a is full day; then b ≥ a ≥ dayAlt ⇒ b is full day too (equal, both permille)
      have hb2 : dayAlt ≤ b := Int.le_trans ha2 h
      have hb1 : ¬ b ≤ nightAlt := by have := band_nonempty; omega
      rw [if_pos ha2, if_neg hb1, if_pos hb2]
      exact Int.le_refl _
    · rw [if_neg ha2]
      have hb1 : ¬ b ≤ nightAlt := by have := band_nonempty; omega
      rw [if_neg hb1]
      by_cases hb2 : dayAlt ≤ b
      · -- a on ramp ≤ permille ≤ (b full day = permille)
        rw [if_pos hb2]
        have hub := workFraction_le_permille a
        unfold workFraction at hub
        rw [if_neg ha1, if_neg ha2] at hub
        exact hub
      · rw [if_neg hb2]; exact ramp_monotone h

/-- The "fully at work" predicate: workFraction has reached full scale. -/
def atWork (altitude : Int) : Prop := workFraction altitude = permille

/-- The "fully home" predicate: workFraction is zero. -/
def atHome (altitude : Int) : Prop := workFraction altitude = 0

/-- CONTIGUOUS DAYTIME: the agent is fully at work for exactly the up-closed
    interval `altitude ≥ dayAlt` — a single contiguous daytime band. -/
theorem atWork_iff_day (altitude : Int) : atWork altitude ↔ dayAlt ≤ altitude := by
  unfold atWork workFraction nightAlt dayAlt permille bandWidth
  constructor
  · intro h
    split at h
    · exact absurd h (by decide)
    · split at h
      · rename_i hd; exact hd
      · omega
  · intro h
    rw [if_neg (by omega), if_pos h]

/-- CONTIGUOUS NIGHT: the agent is fully home for exactly the down-closed
    interval `altitude ≤ nightAlt`. -/
theorem atHome_iff_night (altitude : Int) : atHome altitude ↔ altitude ≤ nightAlt := by
  unfold atHome workFraction nightAlt dayAlt permille bandWidth
  constructor
  · intro h
    split at h
    · rename_i hn; exact hn
    · split at h
      · exact absurd h (by decide)
      · omega
  · intro h
    rw [if_pos h]

/-- The schedule self-describes the breathing city: at midnight the agent is
    home; at noon (overhead sun) it is at work; the transition is monotone. -/
theorem example_midnight_home : atHome (-900) := by
  unfold atHome workFraction nightAlt dayAlt permille bandWidth; decide

theorem example_noon_work : atWork 900 := by
  unfold atWork workFraction nightAlt dayAlt permille bandWidth; decide

theorem example_dawn_partial :
    0 < workFraction 0 ∧ workFraction 0 < permille := by
  unfold workFraction nightAlt dayAlt permille bandWidth
  refine ⟨by decide, by decide⟩

end Commute
end Gnosis
