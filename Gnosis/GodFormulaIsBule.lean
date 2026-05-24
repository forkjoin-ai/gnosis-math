/-
GodFormulaIsBule.lean — the God Formula is a `+Bule` (three faces), not just a `+1`.

We have been reading the `+1` in `godWeight R v = R - min v R + 1` as "the clinamen".
This module makes the precise refinement Taylor flagged: the `+1` is SPECIFICALLY the
OPPORTUNITY face — one of the three Bule faces (waste / opportunity / diversity =
`SpectralNoiseEquilibrium.BuleyUnit`) — NOT the whole Bule.

The full God-Formula state `(R, v)` carries a complete Bule:
  * `waste       = min v R`     — rejection that fits the budget (the vented face)
  * `opportunity = 1`           — the clinamen floor / surviving potential (the `+1`)
  * `diversity   = R - min v R` — the kept alternatives (the surviving weight)
with `buleyUnitScore = R + 1` (the full Bule budget — the conservation law read as
Bule-score conservation). `godWeight` is the sum of the two KEPT faces
(`opportunity + diversity`); the vented `waste` is the conserved complement
(`godWeight + waste = buleyUnitScore`).

Honest scope: a structural decomposition of the EXISTING `godWeight` into the EXISTING
`BuleyUnit` faces — a checked refinement of "+1 = clinamen" to "+1 = the opportunity
face of a +Bule". Init-only / Rustic Church: mirrors `GodFormula`'s proof style
(`show` + `Nat.*` rewrites; no omega / simp / decide on open goals).
-/
import Gnosis.GodFormula
import Gnosis.SpectralNoiseEquilibrium

namespace Gnosis
namespace GodFormulaIsBule

open Gnosis.SpectralNoiseEquilibrium (BuleyUnit buleyUnitScore)

/-- The Bule unit carried by the God-Formula state `(R, v)`: its three faces. -/
def godStateBule (R v : Nat) : BuleyUnit :=
  { waste := min v R, opportunity := 1, diversity := R - min v R }

/-- The `+1` is SPECIFICALLY the opportunity face (one of three), not the whole Bule. -/
theorem the_plus_one_is_the_opportunity_face (R v : Nat) :
    (godStateBule R v).opportunity = 1 := rfl

/-- `godWeight` is the sum of the two KEPT faces: opportunity (`+1`) `+` diversity. -/
theorem godWeight_is_opportunity_plus_diversity (R v : Nat) :
    godWeight R v
      = (godStateBule R v).opportunity + (godStateBule R v).diversity := by
  show R - min v R + 1 = 1 + (R - min v R)
  exact Nat.add_comm _ _

/-- The full Bule budget: `buleyUnitScore = R + 1` (conservation as Bule-score). -/
theorem godStateBule_score (R v : Nat) :
    buleyUnitScore (godStateBule R v) = R + 1 := by
  show min v R + 1 + (R - min v R) = R + 1
  rw [Nat.add_right_comm, Nat.add_comm (min v R) (R - min v R),
    Nat.sub_add_cancel (Nat.min_le_right v R)]

/-- The kept weight plus the vented waste is the full Bule score: `godWeight + waste = R+1`. -/
theorem godWeight_plus_waste_is_bule_score (R v : Nat) :
    godWeight R v + (godStateBule R v).waste
      = buleyUnitScore (godStateBule R v) := by
  rw [godStateBule_score]
  show R - min v R + 1 + min v R = R + 1
  rw [Nat.add_right_comm, Nat.sub_add_cancel (Nat.min_le_right v R)]

/-- **Master: the God Formula is a `+Bule`.** The `+1` is the opportunity face;
    `godWeight` is `opportunity + diversity`; the Bule score is the full budget `R + 1`;
    and the vented `waste` completes the conservation. -/
theorem god_formula_is_bule (R v : Nat) :
    (godStateBule R v).opportunity = 1
    ∧ godWeight R v = (godStateBule R v).opportunity + (godStateBule R v).diversity
    ∧ buleyUnitScore (godStateBule R v) = R + 1
    ∧ godWeight R v + (godStateBule R v).waste = buleyUnitScore (godStateBule R v) :=
  ⟨the_plus_one_is_the_opportunity_face R v,
   godWeight_is_opportunity_plus_diversity R v,
   godStateBule_score R v,
   godWeight_plus_waste_is_bule_score R v⟩

-- Next exploration: pin the bisided ± bit (decline/accept = waste/diversity poles) vs
-- the abstain/opportunity middle as a fully Bule-parameterized `godWeight` variant, and
-- check whether the vent ×3 dispersal (`buleyUnitScore` of a dispersed unit) matches a
-- three-face refinement constant.

end GodFormulaIsBule
end Gnosis
