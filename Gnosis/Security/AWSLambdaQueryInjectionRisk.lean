import Init
-- AWSLambdaQueryInjectionRisk.lean
-- Anti-thesis: AWS Lambda invocation with user-controlled FunctionName or
-- JSON payload construction from user input carries no injection risk.
-- Refutation: FunctionName enumeration, payload injection, and environment
-- variable injection each yield a strictly positive vulnerability window.

namespace AWSLambdaQueryInjection

-- FunctionName injection: invoke with user-controlled function name
def functionNameRisk (nameLen : Nat) (allowListed : Bool) : Nat :=
  if allowListed then 0 else nameLen + 1

-- Allow-listed function names eliminate invocation enumeration
theorem lambda_function_allowlisted_safe (n : Nat) :
    functionNameRisk n true = 0 := by { simp [functionNameRisk]

-- Unvalidated function name allows cross-function invocation
theorem lambda_function_unvalidated_risk (n : Nat) :
    0 < functionNameRisk n false := by
  simp [functionNameRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Payload injection: JSON payload assembled from user input
def payloadRisk (inputLen : Nat) (jsonValidated : Bool) : Nat :=
  if jsonValidated then 0 else inputLen + 1

theorem lambda_payload_validated_safe (n : Nat) :
    payloadRisk n true = 0 := by { simp [payloadRisk]

theorem lambda_payload_unvalidated_risk (n : Nat) :
    0 < payloadRisk n false := by
  simp [payloadRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Environment variable injection via update_function_configuration
def envVarRisk (valueLen : Nat) (sanitized : Bool) : Nat :=
  if sanitized then 0 else valueLen + 1

theorem lambda_env_var_sanitized_safe (n : Nat) :
    envVarRisk n true = 0 := by { simp [envVarRisk]

theorem lambda_env_var_unsanitized_risk (n : Nat) :
    0 < envVarRisk n false := by
  simp [envVarRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Qualifier injection: user-controlled version/alias in function invocation
def qualifierRisk (qualLen : Nat) (allowListed : Bool) : Nat :=
  if allowListed then 0 else qualLen + 1

theorem lambda_qualifier_allowlisted_safe (n : Nat) :
    qualifierRisk n true = 0 := by { simp [qualifierRisk]

theorem lambda_qualifier_unvalidated_risk (n : Nat) :
    0 < qualifierRisk n false := by
  simp [qualifierRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Event source mapping injection: user-controlled event source ARN
def eventSourceRisk (arnLen : Nat) (allowListed : Bool) : Nat :=
  if allowListed then 0 else arnLen + 1

theorem lambda_event_source_allowlisted_safe (n : Nat) :
    eventSourceRisk n true = 0 := by { simp [eventSourceRisk]

theorem lambda_event_source_unvalidated_risk (n : Nat) :
    0 < eventSourceRisk n false := by
  simp [eventSourceRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Risk monotone in name length
theorem lambda_name_risk_monotone (n m : Nat) (h : n ≤ m) :
    functionNameRisk n false ≤ functionNameRisk m false := by { simp [functionNameRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Net: zero-risk requires allow-listed FunctionName AND validated payload
def netLambdaRisk (inputLen : Nat) (allowListed : Bool) (payloadValidated : Bool) : Nat :=
  functionNameRisk inputLen allowListed + payloadRisk inputLen payloadValidated

theorem lambda_net_risk_zero_fully_mitigated (n : Nat) :
    netLambdaRisk n true true = 0 := by { simp [netLambdaRisk, functionNameRisk, payloadRisk]

theorem lambda_net_risk_pos_unmitigated (n : Nat) :
    0 < netLambdaRisk n false false := by
  simp [netLambdaRisk, functionNameRisk, payloadRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

end AWSLambdaQueryInjection
