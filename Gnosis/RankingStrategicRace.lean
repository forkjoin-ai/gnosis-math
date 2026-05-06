import Init
import Gnosis.NashEquilibrium

/-!
# Strategic “race” (game-theoretic bridge)

`Gnosis.NashEquilibrium` already formalizes **unilateral deviation** as thermodynamic debt: higher
`v` lowers `godWeight`. The **Prisoners’ Dilemma** witness is a concrete **strategic race**: from the
mutual-defect Nash profile, a unilateral move toward cooperation **lowers** your payoff if the other
still defects—yet mutual cooperation **Pareto-dominates** the Nash cell.

This is the minimal `Init`+`GodFormula` game bridge; it does **not** yet couple to `Profile2` or
reporting games over rankings (that would be a follow-on module).
-/

namespace Gnosis
namespace RankingStrategicRace

open NashEquilibrium

/-- Unilateral deviation from the `v=8` Nash debts to the “sucker” `v=10` position drops payoff;
mutual Nash is Pareto-inferior to cooperation at `v=2`. Bundled from `prisoners_dilemma`. -/
theorem strategic_race_prisoners_witness :
    godWeight 10 10 < godWeight 10 8 ∧ godWeight 10 8 < godWeight 10 2 := by
  rcases prisoners_dilemma with ⟨_, _, _, hDev, hPareto⟩
  exact ⟨hDev, hPareto⟩

/-- Full numeric shell of `prisoners_dilemma` for downstream reuse. -/
abbrev strategic_race_prisoners_full := prisoners_dilemma

end RankingStrategicRace
end Gnosis
