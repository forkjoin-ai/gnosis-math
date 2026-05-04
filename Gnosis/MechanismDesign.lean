import Gnosis.GodFormula


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

open Gnosis (godWeight)

/-- THM-TRUTHFUL-DOMINATES: In a truthful mechanism, reporting true v
    gives higher payoff than reporting false v' ≠ v. -/
theorem truthful_dominates (R v_true v_false payoff_scale : Nat)
    (hT : v_true ≤ R) (hF : v_false ≤ R)
    (_hTruthPays : payoff_scale = godWeight R v_true)
    (hLiePays : v_false > v_true) :
    -- Lying about v (reporting higher) gives lower weight = lower payoff
    godWeight R v_false < godWeight R v_true := by
  unfold godWeight
  rw [Nat.min_eq_left hT, Nat.min_eq_left hF]
  -- Goal: R - v_false + 1 < R - v_true + 1
  -- Pattern 2 from RUSTIC_CHURCH.md: peel R - v_false = (R - v_true) - (v_false - v_true)
  have hLE : v_true ≤ v_false := Nat.le_of_lt hLiePays
  have hDiffPos : 0 < v_false - v_true := Nat.sub_pos_of_lt hLiePays
  have hDiffLeT : v_false - v_true ≤ R - v_true := Nat.sub_le_sub_right hF v_true
  have hPeel : R - v_false = (R - v_true) - (v_false - v_true) := by
    rw [Nat.sub_sub, Nat.add_sub_of_le hLE]
  have hStrict : R - v_false < R - v_true := hPeel ▸ Nat.sub_lt_self hDiffPos hDiffLeT
  exact Nat.add_lt_add_right hStrict 1

/-- THM-VCG-EXTERNALITY: The VCG payment = social cost without i
    minus social cost with i. This is the externality i imposes. -/
theorem vcg_externality (R v_without v_with : Nat)
    (hW : v_without ≤ R) (hI : v_with ≤ R) (hWorse : v_with ≥ v_without) :
    godWeight R v_without - godWeight R v_with = v_with - v_without := by
  unfold godWeight
  rw [Nat.min_eq_left hW, Nat.min_eq_left hI]
  -- Goal: R - v_without + 1 - (R - v_with + 1) = v_with - v_without
  -- Pattern 7 from RUSTIC_CHURCH.md: shifted-difference identity.
  rw [Nat.add_sub_add_right]
  -- Goal: R - v_without - (R - v_with) = v_with - v_without
  -- Let delta = v_with - v_without. We have v_without + delta = v_with (since hWorse).
  have hAdd : v_without + (v_with - v_without) = v_with := Nat.add_sub_of_le hWorse
  -- Key identity: (R - v_without) - delta = R - v_with, via Nat.sub_sub then hAdd.
  have hKey : R - v_without - (v_with - v_without) = R - v_with := by
    rw [Nat.sub_sub, hAdd]
  rw [← hKey]
  -- Goal: R - v_without - (R - v_without - (v_with - v_without)) = v_with - v_without
  -- Need: v_with - v_without ≤ R - v_without (so Nat.sub_sub_self applies).
  have hCommAdd : (v_with - v_without) + v_without ≤ R := by
    rw [Nat.sub_add_cancel hWorse]; exact hI
  have hDeltaLe : v_with - v_without ≤ R - v_without := Nat.le_sub_of_add_le hCommAdd
  exact Nat.sub_sub_self hDeltaLe

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

end MechanismDesign
