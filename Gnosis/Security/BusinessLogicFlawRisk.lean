import Init
-- BusinessLogicFlawRisk.lean
-- Anti-thesis: Business logic cannot be exploited by attackers because it
-- requires knowing the application's internal workflow, which is not
-- publicly documented.
-- Refutation: Workflow state is observable through API responses and
-- timing; price tampering, step-skip, and quantity manipulation each
-- yield strictly positive gain when server-side re-validation is absent.

namespace Gnosis.Security.BusinessLogicFlawRisk

-- Price tampering: client-supplied price accepted without server re-validation
def priceTamperingRisk (serverValidatesPrice : Bool) (priceClient priceServer : Nat) : Nat :=
  if serverValidatesPrice then 0
  else if priceClient < priceServer then priceServer - priceClient
  else 0

theorem logic_server_validates_price_safe (c s : Nat) :
    priceTamperingRisk true c s = 0 := by { simp [priceTamperingRisk]

theorem logic_tampered_price_yields_gain (c s : Nat) (h : c < s) :
    0 < priceTamperingRisk false c s := by
  simp [priceTamperingRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Workflow step skip: multi-step process allows jumping to final step
def workflowSkipRisk (currentStep : Nat) (requiredStep : Nat)
    (serverEnforcesOrder : Bool) : Nat :=
  if serverEnforcesOrder then 0
  else if currentStep < requiredStep then requiredStep - currentStep
  else 0

theorem logic_enforced_order_safe (c r : Nat) :
    workflowSkipRisk c r true = 0 := by { simp [workflowSkipRisk]

theorem logic_skipped_steps_risk (c r : Nat) (h : c < r) :
    0 < workflowSkipRisk c r false := by
  simp [workflowSkipRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Negative quantity: negative item count converts purchase to credit
def negativeQuantityRisk (quantityValidated : Bool) (quantity : Int) : Nat :=
  if quantityValidated then 0
  else if quantity < 0 then 1
  else 0

theorem logic_quantity_validated_safe (q : Int) :
    negativeQuantityRisk true q = 0 := by { simp [negativeQuantityRisk]

theorem logic_negative_quantity_risk :
    0 < negativeQuantityRisk false (-1) := by
  simp [negativeQuantityRisk]

-- Coupon stacking: unlimited coupon applications drain merchant margin
def couponStackingRisk (maxCoupons : Nat) (appliedCoupons : Nat) : Nat :=
  if appliedCoupons <= maxCoupons then 0 else appliedCoupons - maxCoupons

theorem logic_within_coupon_limit_safe (a m : Nat) (h : a <= m) :
    couponStackingRisk m a = 0 := by
  simp [couponStackingRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

theorem logic_excess_coupons_risk (a m : Nat) (h : m < a) :
    0 < couponStackingRisk m a := by { simp [couponStackingRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Race condition on inventory: two concurrent purchases of last item both succeed
def inventoryRaceRisk (atomicDecrementUsed : Bool) (concurrentBuyers : Nat) : Nat :=
  if atomicDecrementUsed then 0 else concurrentBuyers

theorem logic_atomic_decrement_safe (n : Nat) :
    inventoryRaceRisk true n = 0 := by { simp [inventoryRaceRisk]

theorem logic_non_atomic_race_risk (n : Nat) (h : 0 < n) :
    0 < inventoryRaceRisk false n := by
  simp [inventoryRaceRisk]; exact h

-- Risk monotone in skipped steps
theorem logic_skip_risk_monotone (c r1 r2 : Nat) (h : r1 <= r2) (hc : c < r1) :
    workflowSkipRisk c r1 false <= workflowSkipRisk c r2 false := by
  simp [workflowSkipRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Net: zero-risk requires server price validation, enforced order, quantity check
def netBusinessLogicRisk (priceValidated : Bool) (orderEnforced : Bool)
    (qtyValidated : Bool) : Nat :=
  priceTamperingRisk priceValidated 0 1 +
  workflowSkipRisk 0 1 orderEnforced +
  negativeQuantityRisk qtyValidated (-1)

theorem logic_net_risk_zero_fully_mitigated :
    netBusinessLogicRisk true true true = 0 := by { simp [netBusinessLogicRisk, priceTamperingRisk, workflowSkipRisk, negativeQuantityRisk]

theorem logic_net_risk_pos_unmitigated :
    0 < netBusinessLogicRisk false false false := by
  simp [netBusinessLogicRisk, priceTamperingRisk, workflowSkipRisk, negativeQuantityRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

end BusinessLogicFlawRisk
