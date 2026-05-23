import Init
import Gnosis.Body.ParetoFront
import Gnosis.Body.AmnesiaGritFrontier

/-!
# Life Is A Bitch

What the Pareto front *means*, formalized. On the amnesia↔grit frontier you
cannot have it all: every gain on one axis is paid for on another, the trade is
strict and unavoidable, and there is no single best life — efficiency is
everywhere, the optimum is nowhere. That is the precise content of "life is a
bitch": not pessimism, but the geometry of a genuine Pareto frontier.

Built on `Gnosis/Body/ParetoFront.lean` (the all-pairs antichain) and
`Gnosis/Body/AmnesiaGritFrontier.lean` (the strict adaptability decrease).
-/

namespace Gnosis.Body.LifeIsABitch

open Gnosis.Body.ParetoFront
open Gnosis.Body.AmnesiaGritFrontier

/-- **Every gain forces a sacrifice.** To bank more memory (higher retention)
    you strictly lose adaptability — the second coordinate of the frontier point
    falls. The trade is not optional; it is strict. -/
theorem gain_forces_sacrifice (m scale r1 r2 : Nat) (hlt : r1 < r2) (hle : r2 ≤ scale) :
    (point m scale r2).2 < (point m scale r1).2 := by
  show adaptability r2 scale < adaptability r1 scale
  exact adaptability_strictly_decreases r1 r2 scale hlt hle

/-- **No free lunch.** No frontier option dominates another: you can never be at
    least as well off on both axes and strictly better on one. (The all-pairs
    antichain.) -/
theorem no_free_lunch (m scale : Nat) (hm : 0 < m) :
    ∀ r1 r2, r1 ≤ scale → r2 ≤ scale → r1 ≠ r2 →
      retain m r1 scale ≠ retain m r2 scale →
      ¬ dominates (point m scale r1) (point m scale r2) :=
  frontier_is_an_antichain m scale hm

/-- **The optimum is nowhere.** Every point on the frontier is non-dominated —
    so there is no single best policy; whichever you pick, another is better on
    some axis. You must always choose what to give up. -/
theorem optimum_is_nowhere (m scale : Nat) (hm : 0 < m) :
    ∀ r, r ≤ scale →
      ¬ ∃ r', r' ≤ scale ∧ r' ≠ r ∧
        retain m r' scale ≠ retain m r scale ∧
        dominates (point m scale r') (point m scale r) :=
  pareto_optimal_everywhere m scale hm

/-- **Life is a bitch.** The composed meaning: every gain forces a strict
    sacrifice; there is no free lunch (no domination anywhere); and the optimum
    is nowhere (every option is non-dominated, so no single best life exists).
    The Pareto front is the wall of trades you cannot escape. -/
theorem life_is_a_bitch (m scale : Nat) (hm : 0 < m) :
    (∀ r1 r2, r1 < r2 → r2 ≤ scale → (point m scale r2).2 < (point m scale r1).2) ∧
    (∀ r1 r2, r1 ≤ scale → r2 ≤ scale → r1 ≠ r2 →
      retain m r1 scale ≠ retain m r2 scale →
      ¬ dominates (point m scale r1) (point m scale r2)) ∧
    (∀ r, r ≤ scale →
      ¬ ∃ r', r' ≤ scale ∧ r' ≠ r ∧
        retain m r' scale ≠ retain m r scale ∧
        dominates (point m scale r') (point m scale r)) :=
  ⟨fun r1 r2 h hle => gain_forces_sacrifice m scale r1 r2 h hle,
   no_free_lunch m scale hm,
   optimum_is_nowhere m scale hm⟩

end Gnosis.Body.LifeIsABitch
