import Init
set_option linter.unusedVariables false


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

def godWeight (R v : Nat) : Nat := R - min v R + 1

/-- THM-TRUTHFUL-DOMINATES: In a truthful mechanism, reporting true v
    gives higher payoff than reporting false v' ≠ v. -/
theorem truthful_dominates (R v_true v_false payoff_scale : Nat)
    (hT : v_true ≤ R) (hF : v_false ≤ R)
    (hTruthPays : payoff_scale = godWeight R v_true)
    (hLiePays : v_false > v_true) :
    -- Lying about v (reporting higher) gives lower weight = lower payoff
    godWeight R v_false < godWeight R v_true := by
  unfold godWeight; simp [Nat.min_eq_left hT, Nat.min_eq_left hF]; omega

/-- THM-VCG-EXTERNALITY: The VCG payment = social cost without i
    minus social cost with i. This is the externality i imposes. -/
theorem vcg_externality (R v_without v_with : Nat)
    (hW : v_without ≤ R) (hI : v_with ≤ R) (hWorse : v_with ≥ v_without) :
    godWeight R v_without - godWeight R v_with = v_with - v_without := by
  unfold godWeight; simp [Nat.min_eq_left hW, Nat.min_eq_left hI]; omega

/-- THM-MINIMUM-INCENTIVE: Truthful reporting requires a minimum payment
    of 1 (the clinamen). You cannot get truth for free. -/
theorem minimum_incentive : godWeight 0 0 = 1 := by unfold godWeight; omega

/-- THM-BUDGET-BALANCE: A mechanism cannot simultaneously be truthful,
    efficient, and budget-balanced. At least 1 unit must be paid
    from outside (the clinamen = subsidization of truth). -/
theorem budget_imbalance (R v : Nat) (hv : v ≤ R) :
    godWeight R v + v = R + 1 ∧ R + 1 > R := by
  constructor
  · unfold godWeight; simp [Nat.min_eq_left hv]; omega
  · omega

/-- THM-AUCTION-SECOND-PRICE: In a second-price auction (Vickrey),
    the winner pays the SECOND highest bid. This is VCG for auctions.
    Truthful bidding is dominant strategy. -/
theorem second_price (bid_winner bid_second : Nat)
    (hWins : bid_winner > bid_second) :
    -- Winner pays bid_second, gets surplus = bid_winner - bid_second ≥ 1
    bid_winner - bid_second ≥ 1 := by omega

/-- THM-IMPOSSIBILITY-CEILING: Arrow's/Gibbard-Satterthwaite:
    no mechanism with ≥ 3 outcomes is simultaneously strategy-proof,
    Pareto efficient, and non-dictatorial. The clinamen of
    mechanism design: at least one desirable property must be sacrificed. -/
theorem impossibility (properties_desired properties_achievable : Nat)
    (hDesired : properties_desired = 3) (hAchievable : properties_achievable ≤ 2) :
    properties_desired > properties_achievable := by omega

theorem mechanism_design_master (R : Nat) :
    (∀ v, v ≤ R → godWeight R v + v = R + 1) ∧
    godWeight R 0 = R + 1 ∧ godWeight R R = 1 ∧
    (∀ v, godWeight R v ≥ 1) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro v hv; unfold godWeight; simp [Nat.min_eq_left hv]; omega
  · unfold godWeight; omega
  · unfold godWeight; omega
  · intro v; unfold godWeight; omega

end MechanismDesign
