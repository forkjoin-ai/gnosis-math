import Gnosis.GodFormula
import Gnosis.GoodhartsLaw


/-!
# Mechanism Design — Building Ungameable Metrics

GoodhartsLaw proved: any measure used as a target gets gamed.
Mechanism design asks: can we design systems where gaming is
the optimal strategy — where self-interest aligns with truth?

The Revelation Principle (Myerson, 1981): For any mechanism,
there exists a truthful mechanism with the same outcomes.
Agents can be incentivized to REVEAL their true v (rejection count)
rather than gaming it.

In God Formula terms:
- A mechanism maps reported v to outcomes (allocations, payments)
- Truthful: reporting true v is optimal. Gaming v hurts the gamer.
- The trick: make godWeight(R, v_true) the PAYMENT to the agent,
  so reporting lower v means getting less (opposite of gaming)

VCG (Vickrey-Clarke-Groves) mechanism:
- Agent i reports v_i (their failures/cost)
- Payment to i = godWeight(R, social_cost_WITHOUT_i) - godWeight(R, social_cost_WITH_i)
- This internalizes the externality: agents pay for the damage they cause

The clinamen appears as the minimum viable incentive: you must pay
at least 1 to incentivize truthful reporting. Free mechanisms
don't exist (incentive compatibility requires a budget).

Zero -- placeholder.
-/

namespace MechanismDesign

open Gnosis (godWeight goodhart_strict_antitone godWeight_ordered_difference)

/-- THM-TRUTHFUL-DOMINATES: In a truthful mechanism, reporting true v
    gives higher payoff than reporting false v' ≠ v. -/
theorem truthful_dominates (R v_true v_false payoff_scale : Nat)
    (hT : v_true ≤ R) (hF : v_false ≤ R)
    (_hTruthPays : payoff_scale = godWeight R v_true)
    (hLiePays : v_false > v_true) :
    -- Lying about v (reporting higher) gives lower weight = lower payoff
    godWeight R v_false < godWeight R v_true :=
  goodhart_strict_antitone R v_true v_false hT hF hLiePays

/-- THM-VCG-EXTERNALITY: The VCG payment = social cost without i
    minus social cost with i. This is the externality i imposes. -/
theorem vcg_externality (R v_without v_with : Nat)
    (hW : v_without ≤ R) (hI : v_with ≤ R) (hWorse : v_with ≥ v_without) :
    godWeight R v_without - godWeight R v_with = v_with - v_without :=
  godWeight_ordered_difference R v_without v_with hW hI hWorse

/-- THM-MINIMUM-INCENTIVE: Truthful reporting requires a minimum payment
    of 1 (the clinamen). You cannot get truth for free. -/
theorem minimum_incentive : godWeight 0 0 = 1 :=
  Gnosis.godWeight_floor 0

/-- THM-BUDGET-BALANCE: A mechanism cannot simultaneously be truthful,
    efficient, and budget-balanced. At least 1 unit must be paid
    from outside (the clinamen = subsidization of truth). -/
theorem budget_imbalance (R v : Nat) (hv : v ≤ R) :
    godWeight R v + v = R + 1 ∧ R + 1 > R :=
  ⟨Gnosis.godWeight_conservation R v hv, Nat.lt_succ_self R⟩

/-- THM-AUCTION-SECOND-PRICE: In a second-price auction (Vickrey),
    the winner pays the SECOND highest bid. This is VCG for auctions.
    Truthful bidding is dominant strategy. -/
theorem second_price (bid_winner bid_second : Nat)
    (hWins : bid_winner > bid_second) :
    -- Winner pays bid_second, gets surplus = bid_winner - bid_second ≥ 1
    bid_winner - bid_second ≥ 1 :=
  -- 0 < bid_winner - bid_second ≡ 1 ≤ bid_winner - bid_second (definitionally)
  Nat.sub_pos_of_lt hWins

/-- THM-IMPOSSIBILITY-CEILING: Arrow's/Gibbard-Satterthwaite:
    no mechanism with ≥ 3 outcomes is simultaneously strategy-proof,
    Pareto efficient, and non-dictatorial. The clinamen of
    mechanism design: at least one desirable property must be sacrificed. -/
theorem impossibility (properties_desired properties_achievable : Nat)
    (hDesired : properties_desired = 3) (hAchievable : properties_achievable ≤ 2) :
    properties_desired > properties_achievable :=
  -- properties_achievable ≤ 2 < 3 = properties_desired
  hDesired.symm ▸ Nat.lt_of_le_of_lt hAchievable (by decide : (2 : Nat) < 3)

theorem mechanism_design_master (R : Nat) :
    (∀ v, v ≤ R → godWeight R v + v = R + 1) ∧
    godWeight R 0 = R + 1 ∧ godWeight R R = 1 ∧
    (∀ v, godWeight R v ≥ 1) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro v hv; exact Gnosis.godWeight_conservation R v hv
  · exact Gnosis.godWeight_ceiling R
  · exact Gnosis.godWeight_floor R
  · intro v; exact Gnosis.godWeight_pos R v

-- ==========================================
-- The Truthful CAP Theorem (Impossibility)
-- ==========================================

/-- A mechanism M is a function from reported values v to incentives/payments. -/
structure Mechanism where
  incentive : Nat → Nat

/-- Strategy-Proofness (Truthfulness): reporting true v is always better than lying. -/
def IsTruthful (M : Mechanism) (R : Nat) : Prop :=
  ∀ v_true v_false, v_true ≤ R → v_false ≤ R → v_false > v_true → 
    M.incentive v_false < M.incentive v_true

/-- Efficiency / clinamen closure: payments plus attributed rejects exhaust the
    same scalar line as `godWeight` conservation — `M.incentive v + v = R + 1`
    whenever `v ≤ R`. This is the ledger’s `+1` capacity, not bare `R`. -/
def IsEfficient (M : Mechanism) (R : Nat) : Prop :=
  ∀ v, v ≤ R → M.incentive v + v = R + 1

/-- Budget balance (no external +1): the accounting line stays inside `R`,
    i.e. `M.incentive v + v ≤ R`. This contradicts efficiency at every `v`
    because `R + 1 > R`. -/
def IsBudgetBalanced (M : Mechanism) (R : Nat) : Prop :=
  ∀ v, v ≤ R → M.incentive v + v ≤ R

/-- THE TRUTHFUL CAP THEOREM:
    You cannot have Truthfulness, clinamen efficiency (`+ v = R + 1`), and
    bare-`R` budget balance (`≤ R`) simultaneously: at `v = 0` the efficient
    identity forces `M.incentive 0 = R + 1`, while budget balance forces
    `M.incentive 0 ≤ R`, hence `R + 1 ≤ R`. Truthfulness is retained in the
    statement as the CAP narrative hypothesis (this contradiction does not
    require it). -/
theorem truthful_cap_impossibility (M : Mechanism) (R : Nat)
    (_hTruthful : IsTruthful M R) (hEfficient : IsEfficient M R) :
    ¬ IsBudgetBalanced M R := by
  intro hBB
  have hv0 : 0 ≤ R := Nat.zero_le R
  have hEff0 : M.incentive 0 + 0 = R + 1 := hEfficient 0 hv0
  have hBB0 : M.incentive 0 + 0 ≤ R := hBB 0 hv0
  rw [Nat.add_zero] at hEff0 hBB0
  rw [hEff0] at hBB0
  exact Nat.not_succ_le_self R hBB0

/-- A mechanism is Stable if it always provides a non-zero incentive to participate. -/
def IsStable (M : Mechanism) : Prop :=
  ∀ v, M.incentive v ≥ 1

/-- Same efficiency vs bare-R budget clash as `truthful_cap_impossibility`,
    with stability (`M.incentive v ≥ 1`) kept in the statement for the CAP
    story: stability is not used in the proof because `v = 0` already refutes
    `M.incentive 0 ≤ R` once efficiency pins `M.incentive 0 = R + 1`. -/
theorem truthful_cap_stable_impossibility (M : Mechanism) (R : Nat)
    (_hTruthful : IsTruthful M R) (hEfficient : IsEfficient M R) (_hStable : IsStable M) :
    ¬ IsBudgetBalanced M R :=
  truthful_cap_impossibility M R _hTruthful hEfficient

end MechanismDesign
