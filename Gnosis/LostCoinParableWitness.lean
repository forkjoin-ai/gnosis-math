/-
  Lost coin (Luke 15:8–10): ten silver coins, one lost — lamp, sweep, search, find,
  rejoicing. **`Nat` mnemonic `9 + 1 = 10`** mirrors **`LostSheepParableWitness`**
  (**`99 + 1 = 100`**) at smaller **fold budget** `R = 9`. Same **`godWeight`**
  spine: ceiling **`godWeight R 0 = R + 1`**, conservation at **`v = 1`**.
  Wired to kernels (`ZenosArrowWitness`, `AchillesTortoiseLadder`, `InfinityPath`)
  in `lostCoinStructuralWitness`. Luke 15 trilogy in-repo: **`LostSheepParableWitness`**
  → this module → **`LukeProdigalSonParableWitness`**.

  **Search cost tags:** lamp / sweeping are **surface / active void-walk** labels only — not modeled as extra `Nat` clocks here.

  **Prospect theory (Kahneman / Tversky — on its face, internal reads):** the parable fixes a **reference
  endowment** (**ten** coins) then **loss** of **one**; active search to **recover the loss** is the natural
  prospect-theoretic move (losses weighted relative to the reference state). See
  `docs/ebooks/174-behavioral-taxonomy-structured-dataset/ch04-cognitive-biases.md` (loss aversion / decision
  weights) and Kahneman dual-process routing in
  `docs/ebooks/157-void-attention-cognition-personality/ch08-hologram-vs-halogram.md`,
  `docs/ebooks/81-halograms-visual-personas-and-metacognitive-guidance/ch02-system-1-and-system-2-cognition.md`.
  **Rational** in this module = structural, not vNM: closing the mnemonic **requires** the succ-one strip
  **`godWeight R 0 = R + 1`** (`searcher_rationally_targets_succ_one_residual`). Discharge:
  `prospectTheoryStragglerSearchFaceValueRational`.
-/

import Init
import Gnosis.AchillesTortoiseLadder
import Gnosis.GodFormula
import Gnosis.InfinityPath
import Gnosis.ZenosArrowWitness

namespace LostCoinParableWitness

open Gnosis

/-- Luke 15:8–9 (common English) — counts shadow `10 = 9 + 1`. -/
def luke15_8_quote : String :=
  "Or what woman, having ten silver coins, if she loses one coin, does not light a lamp, "
    ++ "sweep the house, and search carefully until she finds it?"

abbrev tenCoinAggregateLeavesOneHole (claim : Prop) : Prop :=
  claim

abbrev lampAndSweepCostOfActiveSearch (claim : Prop) : Prop :=
  claim

abbrev oneDrachmaDistinctFromFoldNine (claim : Prop) : Prop :=
  claim

abbrev recoveryJoyElevatesWitnessOfOne (claim : Prop) : Prop :=
  claim

/--
  Ledger tag: Kahneman–Tversky-style **prospect / loss** framing on the **one-lost** unit + **rational** succ-one
  spine (`searcher_rationally_targets_succ_one_residual`); see module doc paths.
-/
abbrev prospectTheoryStragglerSearchFaceValueRational (claim : Prop) : Prop :=
  claim

structure LostCoinWitness (agg search distinct joy : Prop) where
  tenfold : tenCoinAggregateLeavesOneHole agg
  search : lampAndSweepCostOfActiveSearch search
  drachma : oneDrachmaDistinctFromFoldNine distinct
  rejoice : recoveryJoyElevatesWitnessOfOne joy

theorem lost_coin_conjuncts (A S D J : Prop) (w : LostCoinWitness A S D J) : A ∧ S ∧ D ∧ J :=
  And.intro w.tenfold (And.intro w.search (And.intro w.drachma w.rejoice))

def buildLostCoinWitness (A S D J : Prop) (hA : A) (hS : S) (hD : D) (hJ : J) :
    LostCoinWitness A S D J :=
  ⟨hA, hS, hD, hJ⟩

/-- Coins counted / safe in the mnemonic fold before recovery of the stray. -/
def toyFoldCoins : Nat := 9

/-- The single sought drachma (strict minority vs the nine-fold). -/
def toySoughtCoin : Nat := 1

/-- Total mnemonic count (ten coins). -/
def toyTotalCoins : Nat := 10

theorem toy_fold_plus_seeker_eq_ten : toyFoldCoins + toySoughtCoin = toyTotalCoins :=
  rfl

theorem toy_seeker_strict_minority : toySoughtCoin < toyFoldCoins := by
  decide

/-! ### God formula specialization (`GodFormula.godWeight`)

Read `toyFoldCoins` as **`R`**, `toySoughtCoin` as one rejection unit **`v`**.
 **`9 + 1 = godWeight 9 0`**; **`godWeight_conservation`** at **`v = 1`. -/

theorem mnemonic_matches_godweight_ceiling :
    toyFoldCoins + toySoughtCoin = godWeight toyFoldCoins 0 := by
  rw [godWeight_ceiling]
  simp only [toySoughtCoin]

/-- Ceiling **`R + 1`**: searcher’s rational target is the universal succ-one / clinamen. -/
theorem searcher_rationally_targets_succ_one_residual :
    godWeight toyFoldCoins 0 = toyFoldCoins + 1 :=
  godWeight_ceiling toyFoldCoins

theorem godweight_ceiling_eq_totalCoins : godWeight toyFoldCoins 0 = toyTotalCoins :=
  mnemonic_matches_godweight_ceiling.symm.trans toy_fold_plus_seeker_eq_ten

theorem soughtcoin_le_fold : toySoughtCoin ≤ toyFoldCoins :=
  Nat.le_of_succ_le toy_seeker_strict_minority

theorem godweight_one_lost_conservation :
    godWeight toyFoldCoins toySoughtCoin + toySoughtCoin = toyFoldCoins + 1 :=
  godWeight_conservation toyFoldCoins toySoughtCoin soughtcoin_le_fold

theorem godweight_one_lost_inner_weight :
    godWeight toyFoldCoins toySoughtCoin = toyTotalCoins - toySoughtCoin := by
  unfold godWeight
  rw [Nat.min_eq_left soughtcoin_le_fold]
  simp only [toyFoldCoins, toySoughtCoin, toyTotalCoins]

theorem godweight_full_fold_rejection_floor : godWeight toyFoldCoins toyFoldCoins = 1 :=
  godWeight_floor toyFoldCoins

theorem lost_coin_god_formula_bundle :
    toyFoldCoins + toySoughtCoin = godWeight toyFoldCoins 0
    ∧ godWeight toyFoldCoins toySoughtCoin + toySoughtCoin = toyFoldCoins + 1
    ∧ godWeight toyFoldCoins toyFoldCoins = 1 :=
  ⟨mnemonic_matches_godweight_ceiling, godweight_one_lost_conservation,
    godweight_full_fold_rejection_floor⟩

/--
  Ledger tag: ceiling **`godWeight R 0 = R + 1`** on the ten-drachma spine — parallels
  `LostSheepParableWitness.lostShepherdPlusOneAnchoredInSuccResidual` (Luke 15 trio).
-/
abbrev lostCoinBearerPlusOneAnchoredInSuccResidual (claim : Prop) : Prop :=
  claim

abbrev propOf {p : Prop} (_ : p) : Prop :=
  p

def LostCoinStructuralWitness : Prop :=
  (toyFoldCoins + toySoughtCoin = toyTotalCoins ∧ toySoughtCoin < toyFoldCoins)
    ∧ (propOf Gnosis.ZenosArrowWitness.arrows_at_rest_trajectory_moves_witness
      ∧ propOf Gnosis.AchillesTortoiseLadder.achilles_tortoise_witness
      ∧ Gnosis.InfinityPath.ladderPath.span = 12)

theorem lostCoinStructuralWitness : LostCoinStructuralWitness :=
  And.intro (And.intro toy_fold_plus_seeker_eq_ten toy_seeker_strict_minority)
    (And.intro Gnosis.ZenosArrowWitness.arrows_at_rest_trajectory_moves_witness
      (And.intro Gnosis.AchillesTortoiseLadder.achilles_tortoise_witness
        Gnosis.InfinityPath.ladder_span))

abbrev void_at_god_clinamen :=
  Gnosis.AchillesTortoiseLadder.tortoise_escapes_original_scale

abbrev pursuit_gaps_strictly_decrease :=
  Gnosis.AchillesTortoiseLadder.gaps_strictly_decrease

abbrev ladder_path_station_count :=
  Gnosis.InfinityPath.ladder_stationCount

end LostCoinParableWitness
