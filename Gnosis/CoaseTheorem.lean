import Init
import Gnosis.GodFormula

namespace Gnosis
namespace CoaseTheorem

open Gnosis (godWeight godWeight_ceiling)

/-!
# Coase theorem (zero transaction-cost invariance)

Factory–laundry externality scaffold:
- factory production `q` creates laundry harm,
- legal right may start with either side,
- with zero transaction costs and successful bargaining to `q*`,
  final God-weight is invariant to initial legal assignment.

## `{Past, Present, Future}` read (ontology, not relativistic **time`)

This file does **not** import a causal manifold. Still, **the same bookkeeping triple** `{Past,
Present, Future}` attaches cleanly as **episode labels**:

- **Past.** The **immutable initial entitlement** **`LegalRight`** for the bargaining episode—“who the
  law favors before side-payments reorganize burdens.’’
- **Future.** **`CoaseEnv.optimalQ`** as the stipulated **social target surface** bargaining is taken
  to attain under the efficiency story (the **`q*`** in **`reachesOptimal`**).
- **Present.** **`BargainingUpdate.finalQ`** realized after negotiation—the **actually locked** production/harm pairing.

Retrocausal **closure** belongs to richer temporal modules (**`SkyrmsBuleyEquilibria`**); Coase contributes
only this **minimal three-slot ledger choreography**.

## Nested “levels’’ of minimized friction (**self-similar stacks**)

 **`totalVent`** already **sums two coarse strata**:

1. **`legalVent`** — institutional / contracting wedge (`transactionCost`).
2. **`inefficiencyVent`** — deviation from **`optimalQ`** on the realised allocation.

 Clearing **`totalVent = 0`** forces **both** summands **zero** (see **`totalVent_components_iff`**): you
cannot claim “Coase-complete’’ on one layer while silently bleeding on the other. Repeating the same
 **`legal + inefficiency`** shape at finer institutional scales yields the recurring **tower** motif—each
 storey must hit **its own zero** before the summed vent vanishes.


## Cross-right **shape invariance** (“self-similar’’ across past labels)

Changing **past** entitlement between **`factoryPollute`** and **`laundryClean`** does **not** alter **`combinedValue`** at **`optimalQ`**, hence **not** **`finalWeight`** once **zero wedge + optimal attainment** (`coasean_invariance_zero_tx`).
-/

/-- Initial legal assignment. -/
inductive LegalRight where
  | factoryPollute
  | laundryClean
  deriving DecidableEq, Repr

/-- Environment for a one-dimensional externality. -/
structure CoaseEnv where
  optimalQ : Nat
  transactionCost : Nat
  factoryBenefit : Nat → Nat
  laundryHarm : Nat → Nat

/-- Net social value (efficiency objective), independent of legal title. -/
def netValue (env : CoaseEnv) (q : Nat) : Int :=
  (env.factoryBenefit q : Int) - (env.laundryHarm q : Int)

/-- Bargaining update under a specific legal-right regime. -/
structure BargainingUpdate (env : CoaseEnv) (right : LegalRight) where
  finalQ : Nat
  transfer : Int
  reachesOptimal : finalQ = env.optimalQ

/-- Resource/objective state after bargaining depends only on chosen `q`. -/
def combinedValue {env : CoaseEnv} {right : LegalRight}
    (u : BargainingUpdate env right) : Int :=
  netValue env u.finalQ

theorem combined_value_at_optimal {env : CoaseEnv} {right : LegalRight}
    (u : BargainingUpdate env right) :
    combinedValue u = netValue env env.optimalQ := by
  unfold combinedValue
  rw [u.reachesOptimal]

/-- **Past-label independence** at **`q*`**: any two successful updates share the **same **`netValue`**
surface—the episode’s “future’’ target scrubs entitlement noise from the surplus tally. -/
theorem combined_value_past_label_independence
    {env : CoaseEnv}
    {r₁ r₂ : LegalRight}
    (u₁ : BargainingUpdate env r₁) (u₂ : BargainingUpdate env r₂) :
    combinedValue u₁ = combinedValue u₂ := by
  rw [combined_value_at_optimal u₁, combined_value_at_optimal u₂]

/-- Vent from legal/institutional friction. -/
def legalVent (env : CoaseEnv) : Nat := env.transactionCost

/-- Vent from production inefficiency relative to the optimum. -/
def inefficiencyVent (env : CoaseEnv) (q : Nat) : Nat :=
  if q = env.optimalQ then 0 else 1

/-- Total vent after bargaining. -/
def totalVent {env : CoaseEnv} {right : LegalRight}
    (u : BargainingUpdate env right) : Nat :=
  legalVent env + inefficiencyVent env u.finalQ

theorem totalVent_components_iff {env : CoaseEnv} {right : LegalRight}
    (u : BargainingUpdate env right) :
    totalVent u = 0 ↔ legalVent env = 0 ∧ inefficiencyVent env u.finalQ = 0 := by
  unfold totalVent
  simp [Nat.add_eq_zero_iff]

/-- Both friction **layers** vanish iff their sum does—no partial “pseudo-minimum’'. -/
theorem totalVent_zero_imp_legal_and_ineff_zero {env : CoaseEnv} {right : LegalRight}
    (u : BargainingUpdate env right) (hz : totalVent u = 0) :
    legalVent env = 0 ∧ inefficiencyVent env u.finalQ = 0 :=
  (totalVent_components_iff u).mp hz

theorem legal_and_ineff_zero_imp_total_zero {env : CoaseEnv} {right : LegalRight}
    (u : BargainingUpdate env right)
    (hL : legalVent env = 0) (hI : inefficiencyVent env u.finalQ = 0) :
    totalVent u = 0 :=
  (totalVent_components_iff u).mpr ⟨hL, hI⟩

/-- Final system God-weight after bargaining. -/
def finalWeight (R : Nat) {env : CoaseEnv} {right : LegalRight}
    (u : BargainingUpdate env right) : Nat :=
  godWeight R (totalVent u)

theorem total_vent_zero_of_zero_tx_and_optimal
    {env : CoaseEnv} {right : LegalRight}
    (u : BargainingUpdate env right)
    (hTx : env.transactionCost = 0) :
    totalVent u = 0 := by
  unfold totalVent legalVent inefficiencyVent
  rw [hTx, u.reachesOptimal]
  simp

theorem final_weight_ceiling_of_zero_tx_and_optimal
    (R : Nat) {env : CoaseEnv} {right : LegalRight}
    (u : BargainingUpdate env right)
    (hTx : env.transactionCost = 0) :
    finalWeight R u = R + 1 := by
  unfold finalWeight
  rw [total_vent_zero_of_zero_tx_and_optimal u hTx]
  exact godWeight_ceiling R

/-- Coasean invariance:
with zero transaction cost and bargaining to `q*`, final God-weight does not
depend on initial legal assignment. -/
theorem coasean_invariance_zero_tx
    (R : Nat) (env : CoaseEnv)
    (hTx : env.transactionCost = 0)
    (uFactory : BargainingUpdate env LegalRight.factoryPollute)
    (uLaundry : BargainingUpdate env LegalRight.laundryClean) :
    finalWeight R uFactory = finalWeight R uLaundry := by
  rw [final_weight_ceiling_of_zero_tx_and_optimal R uFactory hTx]
  rw [final_weight_ceiling_of_zero_tx_and_optimal R uLaundry hTx]

/-- Optional stronger statement: both legal regimes land exactly on ceiling. -/
theorem coasean_joint_ceiling
    (R : Nat) (env : CoaseEnv)
    (hTx : env.transactionCost = 0)
    (uFactory : BargainingUpdate env LegalRight.factoryPollute)
    (uLaundry : BargainingUpdate env LegalRight.laundryClean) :
    finalWeight R uFactory = R + 1 ∧ finalWeight R uLaundry = R + 1 := by
  refine ⟨?_, ?_⟩
  · exact final_weight_ceiling_of_zero_tx_and_optimal R uFactory hTx
  · exact final_weight_ceiling_of_zero_tx_and_optimal R uLaundry hTx

end CoaseTheorem
end Gnosis
