/-
  CityDensity.lean
  ================

  Cities SPRAWL before they BUILD UP. Where land is cheap (low population /
  low density) a settlement spreads horizontally in low-rise buildings; only
  when population density rises does it build vertically. So a building's
  allowed HEIGHT must be gated by the settlement's population — a rural town
  (Winters, CA: ~7k) is a few one-to-two-story buildings, never a downtown
  tower; a metropolis (NYC: ~8M) earns skyscrapers.

  This is the recursive-hospitality / Jane-Jacobs "human-scale density"
  right-sizing principle made concrete for the renderer: `storiesForPopulation`
  is the build allowance as a function of population, and it is monotone,
  has a low-rise rural FLOOR (≤ 10k ⇒ exactly 2 stories), and a hard CEILING.

  PROVEN (omega / split, Init-only — NO Mathlib):
    * `rural_is_low_rise`      : every settlement under 10k is exactly 2 stories
                                 (rural areas sprawl, they do not build up).
    * `stories_monotone`       : more population never permits fewer stories.
    * `stories_floored`        : every settlement is at least 2 stories.
    * `stories_capped`         : no settlement exceeds the 50-story ceiling.
  WITNESSED (decide):
    * `winters_is_low_rise`    : Winters (7,214) ⇒ 2 stories — "a few 2-story
                                 buildings", exactly the user's intuition.
    * `metropolis_builds_up`   : a metropolis strictly out-builds a rural town.
-/

import Gnosis.RecursiveHospitality

namespace Gnosis
namespace CityDensity

/-- Allowed building stories as a step-ramp in settlement population. The bottom
    rung is the rural low-rise floor (2 stories); the top is the skyscraper
    ceiling (50). Density (people competing for finite land) is what forces the
    skyline up — below each threshold the town still has room to sprawl. -/
def storiesForPopulation (pop : Nat) : Nat :=
  if pop < 10000 then 2          -- village / rural: sprawl, 1-2 story
  else if pop < 50000 then 3     -- small town
  else if pop < 250000 then 5    -- town
  else if pop < 1000000 then 10  -- small city
  else if pop < 5000000 then 25  -- city
  else 50                        -- metropolis: skyscrapers

/-- RURAL LOW-RISE FLOOR: any settlement under 10,000 people is exactly two
    stories. Rural areas sprawl out — they do not build up. -/
theorem rural_is_low_rise (pop : Nat) (h : pop < 10000) :
    storiesForPopulation pop = 2 := by
  unfold storiesForPopulation
  rw [if_pos h]

/-- Winters, CA (7,214) is a low-rise town: exactly two stories. -/
theorem winters_is_low_rise : storiesForPopulation 7214 = 2 := by
  decide

/-- MONOTONE: a more populous settlement never permits fewer stories. The
    skyline only rises with density. -/
theorem stories_monotone (a b : Nat) (h : a ≤ b) :
    storiesForPopulation a ≤ storiesForPopulation b := by
  unfold storiesForPopulation
  repeat' split
  all_goals omega

/-- FLOOR: every settlement is at least two stories (a place to live). -/
theorem stories_floored (pop : Nat) : 2 ≤ storiesForPopulation pop := by
  unfold storiesForPopulation
  repeat' split
  all_goals omega

/-- CEILING: no settlement exceeds 50 stories (human-scale cap, not infinite). -/
theorem stories_capped (pop : Nat) : storiesForPopulation pop ≤ 50 := by
  unfold storiesForPopulation
  repeat' split
  all_goals omega

/-- A metropolis strictly builds up beyond a rural town — vertical space is
    used exactly where density demands it. -/
theorem metropolis_builds_up : storiesForPopulation 7214 < storiesForPopulation 8000000 := by
  decide

-- ── Tie-back: density-gated height IS a build allowance over the population
--    "foundation". A rural settlement's allowance is the 2-story floor; the
--    metropolis's is the full ceiling. Reads through RecursiveHospitality. ──────
/-- The rural build allowance is exactly the low-rise floor — the settlement
    builds OUT (more foundations) rather than UP. -/
theorem rural_allowance_is_floor :
    RecursiveHospitality.buildAllowance (storiesForPopulation 7214)
      = RecursiveHospitality.buildAllowance 2 := by
  unfold RecursiveHospitality.buildAllowance
  decide

end CityDensity
end Gnosis
