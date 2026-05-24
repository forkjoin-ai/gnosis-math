import Init
-- LLMRateLimitingRisk.lean
-- Anti-thesis: LLMs are just APIs; standard API-gateway rate limiting (requests/second)
-- is sufficient protection. Token consumption per request is bounded by the same logic
-- as payload size for traditional web services — nothing special about the AI case.
-- Refutation: Token-based billing exposes an entirely different attack surface.
-- A single request can consume millions of tokens via prompt amplification (asking
-- the model to expand, repeat, or elaborate at length). Batch APIs allow bulk
-- submission that bypasses per-request throttles while running up per-token cost.
-- Cost-amplification attacks craft prompts that maximise the output-to-input-cost
-- ratio. Denial-of-wallet attacks exhaust prepaid budgets or trigger surprise
-- invoices, effectively denying service without a single dropped packet.
-- Rate limiting on LLM APIs must be applied at the token level, per-user, per-day,
-- with hard cost caps — not just at the HTTP request level.

namespace Gnosis.Security.LLMRateLimitingRisk

-- Token-flood risk: no per-request token cap allows a single call to drain quota
def tokenFloodRisk (perRequestTokenCapSet : Bool)
    (tokenCapEnforced : Bool) : Bool :=
  !perRequestTokenCapSet || !tokenCapEnforced

theorem token_cap_set_and_enforced_safe :
    tokenFloodRisk true true = false := by { simp [tokenFloodRisk]

theorem token_cap_not_set_risky (enforced : Bool) :
    tokenFloodRisk false enforced = true := by
  simp [tokenFloodRisk]

theorem token_cap_set_but_not_enforced_risky :
    tokenFloodRisk true false = true := by
  simp [tokenFloodRisk]

-- Prompt amplification risk: a short prompt produces an enormously long completion
def promptAmplificationRisk (maxOutputTokensLimited : Bool)
    (amplificationRatioMonitored : Bool) : Bool :=
  !maxOutputTokensLimited && !amplificationRatioMonitored

theorem output_tokens_limited_prevents_amplification (monitored : Bool) :
    promptAmplificationRisk true monitored = false := by
  simp [promptAmplificationRisk]

theorem amplification_ratio_monitored_prevents_attack (limited : Bool) :
    promptAmplificationRisk limited true = false := by
  simp [promptAmplificationRisk]

theorem uncapped_unmonitored_amplification_risky :
    promptAmplificationRisk false false = true := by
  simp [promptAmplificationRisk]

-- Batch API abuse: bulk submissions bypass per-request rate limits
def batchAbuseRisk (batchSizeLimited : Bool)
    (batchRateLimitApplied : Bool)
    (batchCostCapped : Bool) : Bool :=
  !batchSizeLimited && !batchRateLimitApplied && !batchCostCapped

theorem batch_size_limited_prevents_abuse (rateLimited costCapped : Bool) :
    batchAbuseRisk true rateLimited costCapped = false := by
  simp [batchAbuseRisk]

theorem batch_rate_limit_applied_prevents_abuse (sizeLimited costCapped : Bool) :
    batchAbuseRisk sizeLimited true costCapped = false := by
  simp [batchAbuseRisk]

theorem batch_cost_cap_prevents_abuse (sizeLimited rateLimited : Bool) :
    batchAbuseRisk sizeLimited rateLimited true = false := by
  simp [batchAbuseRisk]

theorem unlimited_uncapped_batch_risky :
    batchAbuseRisk false false false = true := by
  simp [batchAbuseRisk]

-- Cost amplification: adversarial prompt engineered to maximise token cost
-- cost = inputTokens * inputPrice + outputTokens * outputPrice
-- amplification factor = outputTokens / inputTokens
def costAmplificationFactor (outputTokens : Nat) (inputTokens : Nat) : Nat :=
  if inputTokens = 0 then 0 else outputTokens / inputTokens

def costAmplificationRisk (outputTokens : Nat) (inputTokens : Nat)
    (amplificationThreshold : Nat) : Bool :=
  amplificationThreshold < costAmplificationFactor outputTokens inputTokens

theorem zero_output_no_amplification_risk (input threshold : Nat) (h : 0 < input) :
    costAmplificationRisk 0 input threshold = false := by
  simp [costAmplificationRisk, costAmplificationFactor, h]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

theorem single_token_in_single_token_out_no_risk (threshold : Nat) (h : 0 < threshold) :
    costAmplificationRisk 1 1 threshold = false := by { simp [costAmplificationRisk, costAmplificationFactor]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Denial-of-wallet: total cost exceeds budget, triggering service interruption
def denialOfWalletRisk (estimatedMonthlyCostCents : Nat)
    (monthlyBudgetCents : Nat)
    (hardSpendCapEnabled : Bool) : Bool :=
  monthlyBudgetCents < estimatedMonthlyCostCents && !hardSpendCapEnabled

theorem hard_spend_cap_prevents_wallet_denial (cost budget : Nat) :
    denialOfWalletRisk cost budget true = false := by { simp [denialOfWalletRisk]

theorem within_budget_no_wallet_denial (cost budget : Nat) (h : cost ≤ budget)
    (capEnabled : Bool) :
    denialOfWalletRisk cost budget capEnabled = false := by
  simp [denialOfWalletRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

theorem uncapped_over_budget_wallet_denial_risky (cost budget : Nat) (h : budget < cost) :
    denialOfWalletRisk cost budget false = true := by { simp [denialOfWalletRisk, h]

-- Per-user daily token budget: rate limiting proportional to user tier
def perUserDailyTokenBudget (tierTokens : Nat) (usedTokens : Nat) : Bool :=
  usedTokens ≤ tierTokens

theorem within_tier_budget_permitted (tier used : Nat) (h : used ≤ tier) :
    perUserDailyTokenBudget tier used = true := by
  simp [perUserDailyTokenBudget, h]

theorem exceeded_tier_budget_blocked (tier used : Nat) (h : tier < used) :
    perUserDailyTokenBudget tier used = false := by
  simp [perUserDailyTokenBudget]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Aggregate LLM rate limiting risk vector
def aggregateLLMRateLimitingRisk
    (capSet capEnforced : Bool)
    (outputLimited amplificationMonitored : Bool)
    (batchSizeLimited batchRateLimited batchCostCapped : Bool)
    (hardSpendCap : Bool) : Nat :=
  (if tokenFloodRisk capSet capEnforced then 1 else 0) +
  (if promptAmplificationRisk outputLimited amplificationMonitored then 1 else 0) +
  (if batchAbuseRisk batchSizeLimited batchRateLimited batchCostCapped then 1 else 0) +
  (if hardSpendCap then 0 else 1)

theorem fully_rate_limited_zero_risk :
    aggregateLLMRateLimitingRisk true true true true true true true true = 0 := by { simp [aggregateLLMRateLimitingRisk, tokenFloodRisk, promptAmplificationRisk,
        batchAbuseRisk]

theorem all_rate_limit_controls_missing_max_risk :
    aggregateLLMRateLimitingRisk false false false false false false false false = 4 := by
  simp [aggregateLLMRateLimitingRisk, tokenFloodRisk, promptAmplificationRisk,
        batchAbuseRisk]

theorem llm_rate_limiting_risk_bounded
    (capSet capEnforced : Bool)
    (outputLimited amplificationMonitored : Bool)
    (batchSizeLimited batchRateLimited batchCostCapped : Bool)
    (hardSpendCap : Bool) :
    aggregateLLMRateLimitingRisk
      capSet capEnforced outputLimited amplificationMonitored
      batchSizeLimited batchRateLimited batchCostCapped hardSpendCap ≤ 4 := by
  simp [aggregateLLMRateLimitingRisk]
  split <;> split <;> split <;> split <;> decide

-- Scanner ROI: detecting missing LLM rate limits avoids denial-of-wallet incidents
def llmRateLimitScannerROI (denialOfWalletCostCents : Nat)
    (scannerCostCents : Nat) : Int :=
  (denialOfWalletCostCents : Int) - (scannerCostCents : Int)

theorem llm_rate_limit_scanner_profitable (walletCost scan : Nat) (h : scan < walletCost) :
    0 < llmRateLimitScannerROI walletCost scan := by
  simp [llmRateLimitScannerROI]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Fleet ROI: token-flood risk detection scales linearly with LLM endpoint count
def llmRateLimitFleetROI (detectionValueCents : Nat) (llmEndpoints : Nat) : Nat :=
  detectionValueCents * llmEndpoints

theorem llm_rate_limit_fleet_roi_monotone (v e1 e2 : Nat) (h : e1 ≤ e2) :
    llmRateLimitFleetROI v e1 ≤ llmRateLimitFleetROI v e2 := by
  simp [llmRateLimitFleetROI]
  exact Nat.mul_le_mul_left v h

theorem positive_llm_rate_limit_fleet_roi (v e : Nat) (hv : 0 < v) (he : 0 < e) :
    0 < llmRateLimitFleetROI v e := by
  simp [llmRateLimitFleetROI]
  exact Nat.mul_pos hv he

end LLMRateLimitingRisk
