import Gnosis.RL
import Gnosis.BuleBudgetLedger
import Gnosis.EconomicGain
import Gnosis.NoCloningTaxEqualsBuleCost

/-!
# Rejection training budget ledger bridge

This module connects the RL claim "more trained rejections grow budget" to the
operational bule ledger. Under one-bule-per-rejection accounting, a rejection
training run with `n` rounds spends `n` bule, and the RL budget is exactly the
base budget plus that ledger spend.
-/

namespace Gnosis
namespace RLBudgetLedgerBridge

open Gnosis.BuleBudgetLedger
open Gnosis.EconomicGain
open Gnosis.NoCloningTaxEqualsBuleCost

/-- A single trained rejection is a visible boundary crossing. -/
def rejection_training_measurement_event : MeasurementEvent :=
  { prior_status := .NotYetFalsified
    posterior_status := .FalsifiedByMeasurement
    methodology_witness_count := 1 }

/-- One trained rejection pays exactly one bule by the no-cloning tax model. -/
theorem rejection_training_measurement_cost_eq_one :
    bule_cost_of_measurement rejection_training_measurement_event = 1 := by
  decide

/-- Ledger entry corresponding to one trained rejection round. -/
def rejection_training_spend_entry : BuleSpendEntry :=
  { measurement_label := "rejection-training-round"
    bule_paid := bule_cost_of_measurement rejection_training_measurement_event
    wave_number := 0
    corresponds_to_falsification := true }

/-- The generated ledger for `rounds` trained rejections. -/
def rejection_training_ledger (rounds : Nat) : List BuleSpendEntry :=
  List.replicate rounds rejection_training_spend_entry

/-- Each generated rejection-training ledger spends exactly its round count. -/
theorem rejection_training_ledger_spend_eq_rounds (rounds : Nat) :
    total_bule_spent (rejection_training_ledger rounds) = rounds := by
  induction rounds with
  | zero =>
      decide
  | succ rounds ih =>
      unfold rejection_training_ledger at ih
      unfold rejection_training_spend_entry at ih
      rw [rejection_training_measurement_cost_eq_one] at ih
      unfold rejection_training_ledger
      simp [List.replicate, total_bule_spent, rejection_training_spend_entry,
        rejection_training_measurement_cost_eq_one]
      rw [ih]
      exact Nat.add_comm 1 rounds

/--
Main bridge: under one-bule-per-rejection accounting, RL budget after rejection
training equals base budget plus the bule spend recorded by the generated ledger.
-/
theorem rejection_training_budget_eq_base_plus_ledger_spend (base rounds : Nat) :
    Gnosis.RL.rejectionTrainingBudget base rounds =
      base + total_bule_spent (rejection_training_ledger rounds) := by
  rw [rejection_training_ledger_spend_eq_rounds]
  rfl

/--
Strict bridge: adding positive rejection-training rounds strictly increases the
ledger-backed RL budget.
-/
theorem ledger_backed_rejection_training_strictly_grows
    (base rounds extra : Nat) (h : 0 < extra) :
    base + total_bule_spent (rejection_training_ledger rounds) <
      base + total_bule_spent (rejection_training_ledger (rounds + extra)) := by
  rw [rejection_training_ledger_spend_eq_rounds,
    rejection_training_ledger_spend_eq_rounds]
  exact Nat.add_lt_add_left (Nat.lt_add_of_pos_right h) base

/--
The same ledger spend that grows the RL budget also weakly lowers Buleyean RL
cost when one more rejection signal is added.
-/
theorem ledger_backed_rejection_training_cost_weakly_decreases (rounds : Nat) :
    buleyeanRLCost (total_bule_spent (rejection_training_ledger (rounds + 1))) ≤
      buleyeanRLCost (total_bule_spent (rejection_training_ledger rounds)) := by
  rw [rejection_training_ledger_spend_eq_rounds,
    rejection_training_ledger_spend_eq_rounds]
  exact buleyean_cost_weakly_decreasing rounds

/--
One positive ledger-backed rejection signal is already enough to make Buleyean
RL strictly cheaper than the reward-RL baseline.
-/
theorem positive_ledger_spend_makes_buleyean_rl_strictly_cheaper (rounds : Nat)
    (h : 0 < total_bule_spent (rejection_training_ledger rounds)) :
    buleyeanRLCost (total_bule_spent (rejection_training_ledger rounds)) <
      rewardRLCost := by
  exact buleyean_strictly_cheaper
    (total_bule_spent (rejection_training_ledger rounds)) h

/--
Combined statement: adding positive rejection-training mass strictly increases
ledger-backed budget while weakly decreasing the Buleyean RL cost.
-/
theorem rejection_mass_grows_budget_and_lowers_cost
    (base rounds extra : Nat) (h : 0 < extra) :
    base + total_bule_spent (rejection_training_ledger rounds) <
        base + total_bule_spent (rejection_training_ledger (rounds + extra))
      ∧ buleyeanRLCost (total_bule_spent (rejection_training_ledger (rounds + extra))) ≤
        buleyeanRLCost (total_bule_spent (rejection_training_ledger rounds)) := by
  constructor
  · exact ledger_backed_rejection_training_strictly_grows base rounds extra h
  · rw [rejection_training_ledger_spend_eq_rounds,
      rejection_training_ledger_spend_eq_rounds]
    unfold buleyeanRLCost
    apply Nat.div_le_div_left
    · exact Nat.succ_le_succ (Nat.le_add_right rounds extra)
    · exact Nat.succ_pos rounds

/--
Session bridge: the existing eight-bule session ledger would grow a zero-base RL
training budget to eight if read as rejection-training spend.
-/
theorem session_bule_spend_matches_zero_base_training_budget :
    Gnosis.RL.rejectionTrainingBudget 0 total_session_bule_spent =
      total_session_bule_spent := by
  rw [total_session_bule_spent_eq_8]
  decide

/-- The session's five falsification bule yield a five-unit zero-base RL budget. -/
theorem session_falsification_spend_matches_zero_base_training_budget :
    Gnosis.RL.rejectionTrainingBudget 0 bule_spent_on_falsifications_in_session =
      bule_spent_on_falsifications_in_session := by
  rw [bule_spent_on_falsifications_in_session_eq_5]
  decide

end RLBudgetLedgerBridge
end Gnosis
